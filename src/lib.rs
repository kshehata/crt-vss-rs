extern crate bulletproofs;

use bulletproofs::{BulletproofGens, PedersenGens};
use bulletproofs::r1cs::*;
use curve25519_dalek::{ristretto::CompressedRistretto, scalar::Scalar};
use merlin::Transcript;
use num_bigint::BigUint;
use std::convert::TryInto;

pub fn big_int_to_scalar(bint: BigUint) -> Scalar {
    let mut bits = bint.to_bytes_le();
    assert!(bits.len() <= 32);
    while bits.len() < 32 {
        bits.push(0);
    }
    Scalar::from_bytes_mod_order(bits.try_into().unwrap())
}

pub fn scalar_to_big_int(scalar: Scalar) -> BigUint {
    BigUint::from_bytes_le(scalar.as_bytes())
}

pub fn compute_a(s_ref: &BigUint, p0_ref: &BigUint) -> Vec<BigUint> {
    let mut a_vals = vec![];
    let mut s = s_ref.clone();
    let p0 = p0_ref.clone();
    a_vals.push(&s % &p0);
    s = &s / &p0;
    while s > BigUint::ZERO {
        a_vals.push(&s % &p0);
        s = &s / &p0;
    }
    a_vals
}

pub fn sample_a(s_ref: &BigUint, p0_ref: &BigUint, m_size: usize) -> (BigUint, Vec<BigUint>) {
    let mut a_vals = vec![s_ref.clone()];
    let mut sum = s_ref.clone();
    let mut power_p0 = p0_ref.clone();
    for i in 1..m_size {
        let new_a = scalar_to_big_int(Scalar::random(&mut rand::thread_rng())) % p0_ref.clone();
        a_vals.push(new_a.clone());
        sum = &sum + (&power_p0 * &new_a);
        power_p0 = &power_p0 * p0_ref;
    }
    (sum, a_vals)
}

// Add equations to constrain a value to [0, 2^n).
pub fn add_range_constraints<CS: ConstraintSystem>(
    cs: &mut CS,
    // Variable of value to be constrained
    mut v: LinearCombination,
    // If set, what to assign the wires to.
    v_val: Option<BigUint>,
    // Bit size of value
    n: usize,
) -> Result<(), R1CSError> {
    let mut pow_2 = Scalar::ONE;
    for i in 0..n {
        // Add constraints for bit i
        let (a, b, o) = cs.allocate_multiplier(
            v_val.as_ref().map(|x| {
                let bit: BigUint = (x >> i) & &BigUint::from(true);
                (big_int_to_scalar(bit.clone()), big_int_to_scalar(BigUint::from(true) - bit.clone()))
            }))?;

        // Constrain a * b = 0 so that one of a or b must be zero.
        cs.constrain(o.into());

        // Constrain that a = 1 - b, so that both are either 1 or 0.
        cs.constrain(a + b - Scalar::ONE);

        // Update linear combination v to remove the bit we just constrained.
        v = v - a * pow_2;
        pow_2 = pow_2 + pow_2;
    }

    // Finally enforce that after we've removed all of the bits, the value is zero.
    cs.constrain(v);

    Ok(())
}

// Range proof gadget
struct RangeProof(R1CSProof);

impl RangeProof {
    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        v: BigUint,
        u: BigUint,
        n: usize,
    ) -> Result<(RangeProof, CompressedRistretto), R1CSError> {
        transcript.append_message(b"dom-sep", b"RangeProof");

        let mut prover = Prover::new(&pc_gens, transcript);

        // Should probably accept these as inputs, but for now generate as needed
        let mut blinding_rng = rand::thread_rng();

        let (v_com, v_var)
            = prover.commit(big_int_to_scalar(v.clone()), Scalar::random(&mut blinding_rng));

        assert!(add_range_constraints(&mut prover, v_var.into(), Some(v.clone()), n).is_ok());
        assert!(add_range_constraints(&mut prover, LinearCombination::from(big_int_to_scalar(u.clone())) - v_var, Some(u-v), n).is_ok());

        let proof = prover.prove(&bp_gens)?;

        Ok((RangeProof(proof), v_com))
    }
}

impl RangeProof {
    pub fn verify<'a, 'b>(
        &self,
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        v_com: CompressedRistretto,
        u: BigUint,
        n: usize,
    ) -> Result<(), R1CSError> {
        transcript.append_message(b"dom-sep", b"RangeProof");

        let mut verifier = Verifier::new(transcript);

        let v_var = verifier.commit(v_com);

        assert!(add_range_constraints(&mut verifier, v_var.into(), None, n).is_ok());
        assert!(add_range_constraints(&mut verifier, LinearCombination::from(big_int_to_scalar(u.clone())) - v_var, None, n).is_ok());

        verifier.verify(&self.0, pc_gens, bp_gens)
    }
}

pub fn add_bit_constraints<CS: RandomizedConstraintSystem>(
    cs: &mut CS,
    mut v: LinearCombination,
    v_val: Option<BigUint>,
    n: usize,
    z: Scalar,
) -> Result<LinearCombination, R1CSError> {
    let v_in_range = v_val.clone().map(|x| x < (BigUint::from(true) << n)).unwrap_or(false);
    let mut pow_2 = Scalar::ONE;
    let mut pow_z = Scalar::ONE;
    let mut cp = LinearCombination::from(Scalar::ZERO);
    for i in 0..n {
        // Add constraints for bit i
        // Is there a better way to do this?
        // Basically, if value is in range, then use the bit decompoisition.
        // Otherwise, set the lowest "bit" wire to the value, complement to zero,
        // and all other "bit" wires to 0 and complement to 1.
        let (a, b, o) = cs.allocate_multiplier(
            v_val.as_ref().map(|x| {
                if v_in_range {
                    let bit: BigUint = (x >> i) & BigUint::from(true);
                    (big_int_to_scalar(bit.clone()), big_int_to_scalar(BigUint::from(true) - bit.clone()))
                } else if i == 0 {
                    (big_int_to_scalar(x.clone()), Scalar::ZERO.into())
                } else {
                    (Scalar::ZERO.into(), Scalar::ONE.into())
                }
            }))?;

        // Constrain a * b = 0 so that one of a or b must be zero.
        cs.constrain(o.into());

        // add polynomial constraints for disjunction
        cp = cp + (a + b - Scalar::ONE) * pow_z;
        pow_z = pow_z * z;
        
        // Update linear combination v to remove the bit we just constrained.
        v = v - a * pow_2;
        pow_2 = pow_2 + pow_2;
    }

    // Finally enforce that after we've removed all of the bits, the value is zero.
    cs.constrain(v);

    Ok(cp)
}

// Add constraints for a disjuction of ranges.
// i.e. either v1 is in [0, 2^n) or v2 is in [0, 2^n).
pub fn add_range_disjunction<CS: RandomizableConstraintSystem>(
    cs: &mut CS,
    // Variable of values to be constrained
    v1: LinearCombination,
    v2: LinearCombination,
    // If set, what to assign the wires to.
    v1_val: Option<BigUint>,
    v2_val: Option<BigUint>,
    // Bit size of values
    n1: usize,
    n2: usize,
) -> Result<(), R1CSError> {
    cs.specify_randomized_constraints(move |cs| {
        let z = cs.challenge_scalar(b"disjunction challenge");
        let c1 = add_bit_constraints(cs, v1, v1_val, n1, z)?;
        let c2 = add_bit_constraints(cs, v2, v2_val, n2, z)?;
        // Enforce the disjunction
        let (_, _, c_out) = cs.multiply(c1, c2);
        cs.constrain(c_out.into());
        Ok(())
    })
}

struct DisjunctionOfRanges(R1CSProof);

impl DisjunctionOfRanges {
    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        v1: BigUint,
        v2: BigUint,
        n1: usize,
        n2: usize,
    ) -> Result<(DisjunctionOfRanges, CompressedRistretto, CompressedRistretto), R1CSError> {
        transcript.append_message(b"dom-sep", b"DisjunctionOfRanges");

        let mut prover = Prover::new(&pc_gens, transcript);

        // Should probably accept these as inputs, but for now generate as needed
        let mut blinding_rng = rand::thread_rng();

        let (v1_com, v1_var)
            = prover.commit(big_int_to_scalar(v1.clone()), Scalar::random(&mut blinding_rng));
        let (v2_com, v2_var)
            = prover.commit(big_int_to_scalar(v2.clone()), Scalar::random(&mut blinding_rng));

        assert!(add_range_disjunction(&mut prover, v1_var.into(), v2_var.into(), Some(v1), Some(v2), n1, n2).is_ok());

        let proof = prover.prove(&bp_gens)?;

        Ok((DisjunctionOfRanges(proof), v1_com, v2_com))
    }
}

impl DisjunctionOfRanges {
    pub fn verify<'a, 'b>(
        &self,
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        v1_com: CompressedRistretto,
        v2_com: CompressedRistretto,
        n1: usize,
        n2: usize,
    ) -> Result<(), R1CSError> {
        transcript.append_message(b"dom-sep", b"DisjunctionOfRanges");

        let mut verifier = Verifier::new(transcript);

        let v1_var = verifier.commit(v1_com);
        let v2_var = verifier.commit(v2_com);

        assert!(add_range_disjunction(&mut verifier, v1_var.into(), v2_var.into(), None, None, n1, n2).is_ok());

        verifier.verify(&self.0, pc_gens, bp_gens)
    }
}

// Proof that v = s mod p
// Where s is some value mod p0
pub struct ProofOfMod(R1CSProof);

pub struct ExtendedProofOfMod(R1CSProof);

impl ProofOfMod {
    fn gadget<CS: RandomizableConstraintSystem>(
        cs: &mut CS,
        v: Variable,
        v_val: Option<BigUint>,
        s: Variable,
        s_val: Option<BigUint>,
        p: BigUint,
        p0: BigUint,
        k_val: Option<BigUint>,
    ) -> Result<(), R1CSError> {
        // p0 = q * p + t
        let big_one = BigUint::from(true);
        let (q, t) = (&p0 / &p, &p0 % &p);
        let n1: usize = (p.bits()).try_into().unwrap();
        let n2: usize = (q.bits()).try_into().unwrap();
        let k = cs.allocate(k_val.as_ref().map(|x| big_int_to_scalar(x.clone()))).unwrap();

        // Fundamental constraint for proof of mod
        cs.constrain(v + k * big_int_to_scalar(p.clone()) - s);

        add_range_constraints(cs, v.into(), v_val.clone(), n1)?;
        add_range_constraints(cs, k.into(), k_val.clone(), n2)?;
        add_range_constraints(cs, big_int_to_scalar(&p - &big_one) - v, v_val.as_ref().map(|x| &p - x - &big_one), n1)?;
        add_range_constraints(cs, big_int_to_scalar(q.clone()) - k, k_val.as_ref().map(|x| &q - x), n2)?;
        add_range_disjunction(cs,
            big_int_to_scalar(&t - &big_one) - v,
            big_int_to_scalar(&q - &big_one) - k,
            v_val.as_ref().map(|x| &p0 + &t - &big_one - x),
            k_val.as_ref().map(|x| &q - &big_one - x),
            n1, n2)?;

        Ok(())
    }
}
impl ProofOfMod {
    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        v: BigUint,
        s: BigUint,
        k: BigUint,
        p: BigUint,
        p0: BigUint,
    ) -> Result<(ProofOfMod, CompressedRistretto, CompressedRistretto), R1CSError> {
        transcript.append_message(b"dom-sep", b"ProofOfMod");

        let mut prover = Prover::new(&pc_gens, transcript);

        // Should probably accept these as inputs, but for now generate as needed
        let mut blinding_rng = rand::thread_rng();

        let (v_com, v_var)
            = prover.commit(big_int_to_scalar(v.clone()), Scalar::random(&mut blinding_rng));
        let (s_com, s_var)
            = prover.commit(big_int_to_scalar(s.clone()), Scalar::random(&mut blinding_rng));

        ProofOfMod::gadget(&mut prover, v_var, Some(v), s_var, Some(s), p, p0, Some(k))?;

        let proof = prover.prove(&bp_gens)?;

        Ok((ProofOfMod(proof), v_com, s_com))
    }
}

impl ProofOfMod {
    pub fn verify<'a, 'b>(
        &self,
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        v_com: CompressedRistretto,
        s_com: CompressedRistretto,
        p: BigUint,
        p0: BigUint,
    ) -> Result<(), R1CSError> {
        transcript.append_message(b"dom-sep", b"ProofOfMod");

        let mut verifier = Verifier::new(transcript);

        let v_var = verifier.commit(v_com);
        let s_var = verifier.commit(s_com);

        ProofOfMod::gadget(&mut verifier, v_var, None, s_var, None, p, p0, None)?;

        verifier.verify(&self.0, pc_gens, bp_gens)
    }
}

impl ExtendedProofOfMod {
    fn gadget<CS: RandomizableConstraintSystem>(
        cs: &mut CS,
        a: &Vec<Variable>,
        a_val: &Vec<Option<BigUint>>,
        a_mod: &Vec<Variable>,
        a_mod_val: &Vec<Option<BigUint>>,
        vi: &Vec<Variable>,
        vi_val: &Vec<Option<BigUint>>,
        vi_mod: &Vec<Variable>,
        vi_mod_val: &Vec<Option<BigUint>>,
        p: &BigUint,
        p0: &BigUint,
        v: Variable,
    ) -> Result<(), R1CSError> {
        let t = p0 % p;
        for i in 0..a.len() {
            let k_val = if i < a_val.len() {Option::Some(a_val[i].as_ref().unwrap() / p)} else {None};
            let a_mod_val_i = if i < a_mod_val.len() {Option::Some(a_mod_val[i].as_ref().unwrap().clone())} else {None};
            let a_val_i = if i < a_val.len() {Option::Some(a_val[i].as_ref().unwrap().clone())} else {None};
            
            ProofOfMod::gadget(cs, a_mod[i].clone(), a_mod_val_i, a[i].clone(), a_val_i, p.clone(), p0.clone(), k_val)?;
        }
        
        for i in 0..(vi.len() - 1) {
            let k_val = if i < vi_val.len() {Option::Some(vi_val[i].as_ref().unwrap() / p)} else {None};
            let vi_mod_val_i = if i < vi_mod_val.len() {Option::Some(vi_mod_val[i].as_ref().unwrap().clone())} else {None};
            let vi_val_i = if i < vi_val.len() {Option::Some(vi_val[i].as_ref().unwrap().clone())} else {None};
            cs.constrain(a_mod[i] + big_int_to_scalar(t.clone()) * vi_mod[i + 1] - vi[i]);
            
            ProofOfMod::gadget(cs, vi_mod[i].clone(), vi_mod_val_i, vi[i].clone(), vi_val_i, p.clone(), p0.clone(), k_val)?;
        }
        cs.constrain(v - vi_mod[0].clone());

        Ok(())
    }

    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        v: BigUint,
        a_vals: &Vec<BigUint>,
        p: BigUint,
        p0: BigUint,
    ) -> Result<(ExtendedProofOfMod, CompressedRistretto, Vec<CompressedRistretto>, Vec<CompressedRistretto>, Vec<CompressedRistretto>, Vec<CompressedRistretto>), R1CSError> {
        transcript.append_message(b"dom-sep", b"ExtendedProofOfMod");

        let mut prover = Prover::new(&pc_gens, transcript);

        // // Should probably accept these as inputs, but for now generate as needed
        let mut blinding_rng = rand::thread_rng();

        let (v_com, v_var)
            = prover.commit(big_int_to_scalar(v.clone()), Scalar::random(&mut blinding_rng));
        
        let mut a = vec![];
        let mut a_val = vec![];
        let mut a_com = vec![];
        let mut a_mod = vec![];
        let mut a_mod_com = vec![];
        let mut a_mod_val = vec![];
        let mut vi = vec![];
        let mut vi_val = vec![];
        let mut vi_com = vec![];
        let mut vi_mod = vec![];
        let mut vi_mod_com = vec![];
        let mut vi_mod_val = vec![];

        for i in a_vals.iter() {
            a_val.push(Option::Some((*i).clone()));
            a_mod_val.push(Option::Some(i % &p));
            let (com, var) = prover.commit(big_int_to_scalar((*i).clone()), Scalar::random(&mut blinding_rng));
            a.push(var);
            a_com.push(com);
            let (com, var) = prover.commit(big_int_to_scalar(i % &p), Scalar::random(&mut blinding_rng));
            a_mod.push(var);
            a_mod_com.push(com);
        }

        vi_mod_val.insert(0, a_mod_val[a_val.len() - 1].clone());
        vi_val.insert(0, a_mod_val[a_val.len() - 1].clone());
        
        for i in 0..(a.len() - 1) {
            let v_i = a_mod_val[a.len() - 2 - i].clone().unwrap() + vi_mod_val[0].clone().unwrap() * (&p0 % &p);
            let v_i_mod = &v_i % &p;
            vi_val.insert(0, Option::Some(v_i.clone()));
            vi_mod_val.insert(0, Option::Some(v_i_mod.clone()));
        }

        for i in 0..vi_val.len(){
            let (com, var) = prover.commit(big_int_to_scalar(vi_val[i].clone().unwrap()), Scalar::random(&mut blinding_rng));
            vi.push(var);
            vi_com.push(com);
            let (com, var) = prover.commit(big_int_to_scalar(vi_mod_val[i].clone().unwrap()), Scalar::random(&mut blinding_rng));
            vi_mod.push(var);
            vi_mod_com.push(com);
        }

        ExtendedProofOfMod::gadget(&mut prover, &a, &a_val, &a_mod, &a_mod_val, &vi, &vi_val, &vi_mod, &vi_mod_val, &p, &p0, v_var)?;

        let proof = prover.prove(&bp_gens)?;

        Ok((ExtendedProofOfMod(proof), v_com, a_com, a_mod_com, vi_com, vi_mod_com))
    }

    pub fn verify<'a, 'b>(
        &self,
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        v_com: CompressedRistretto,
        a_com: &Vec<CompressedRistretto>,
        a_mod_com: &Vec<CompressedRistretto>,
        vi_com: &Vec<CompressedRistretto>,
        vi_mod_com: &Vec<CompressedRistretto>,
        p: BigUint,
        p0: BigUint,
    ) -> Result<(), R1CSError> {
        transcript.append_message(b"dom-sep", b"ExtendedProofOfMod");

        let mut verifier = Verifier::new(transcript);

        let v_var = verifier.commit(v_com);
        
        let mut a = vec![];
        let mut a_mod = vec![];

        let mut vi = vec![];
        let mut vi_mod = vec![];

        for i in 0..a_com.len() {
            let a_var = verifier.commit(a_com[i].clone());
            a.push(a_var);
            let a_mod_var = verifier.commit(a_mod_com[i].clone());
            a_mod.push(a_mod_var);
        }

        for i in 0..vi_com.len() {
            let vi_var = verifier.commit(vi_com[i].clone());
            vi.push(vi_var);
            let vi_mod_var = verifier.commit(vi_mod_com[i].clone());
            vi_mod.push(vi_mod_var);
        }

        ExtendedProofOfMod::gadget(&mut verifier, &a, &vec![], &a_mod, &vec![], &vi, &vec![], &vi_mod, &vec![], &p, &p0, v_var)?;

        verifier.verify(&self.0, pc_gens, bp_gens)
    }

    pub fn share<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        s: BigUint,
        weights: &Vec<BigUint>,
        p0: BigUint,
    ) -> Result<(ExtendedProofOfMod, CompressedRistretto, Vec<CompressedRistretto>, Vec<CompressedRistretto>, Vec<Vec<CompressedRistretto>>, 
        Vec<Vec<CompressedRistretto>>, Vec<Vec<CompressedRistretto>>), R1CSError> {

        transcript.append_message(b"dom-sep", b"AggregatedExtendedProofOfMod");        

        let mut prover = Prover::new(&pc_gens, transcript);

        // // Should probably accept these as inputs, but for now generate as needed
        let mut blinding_rng = rand::thread_rng();

        let (s_com, s_var)
            = prover.commit(big_int_to_scalar(s.clone()), Scalar::random(&mut blinding_rng));
        
        let mut combined_a_mod_com = vec![];
        let mut combined_vi_com = vec![];
        let mut combined_vi_mod_com = vec![];
        let mut v_com = vec![];
        let mut a = vec![];
        let mut a_val = vec![];
        let mut a_com = vec![];

        let (s, a_vals) = sample_a(&s, &p0, 1);
        for i in a_vals.iter() {
            a_val.push(Option::Some((*i).clone()));
            let (com, var) = prover.commit(big_int_to_scalar((*i).clone()), Scalar::random(&mut blinding_rng));
            a.push(var);
            a_com.push(com);
        }
        prover.constrain(s_var - a[0]);

        for p in weights.iter() {
            let v = &s % p;
            let (com, v_var)
                = prover.commit(big_int_to_scalar(v.clone()), Scalar::random(&mut blinding_rng));
            v_com.push(com);

            let mut a_mod = vec![];
            let mut a_mod_com = vec![];
            let mut a_mod_val = vec![];
            let mut vi = vec![];
            let mut vi_val = vec![];
            let mut vi_com = vec![];
            let mut vi_mod = vec![];
            let mut vi_mod_com = vec![];
            let mut vi_mod_val = vec![];

            for i in a_vals.iter() {
                a_mod_val.push(Option::Some(i % p));
                let (com, var) = prover.commit(big_int_to_scalar(i % p), Scalar::random(&mut blinding_rng));
                a_mod.push(var);
                a_mod_com.push(com);
            }

            vi_mod_val.insert(0, a_mod_val[a_val.len() - 1].clone());
            vi_val.insert(0, a_mod_val[a_val.len() - 1].clone());
            
            for i in 0..(a.len() - 1) {
                let v_i = a_mod_val[a.len() - 2 - i].clone().unwrap() + vi_mod_val[0].clone().unwrap() * (&p0 % p);
                let v_i_mod = &v_i % p;
                vi_val.insert(0, Option::Some(v_i.clone()));
                vi_mod_val.insert(0, Option::Some(v_i_mod.clone()));
            }

            for i in 0..vi_val.len(){
                let (com, var) = prover.commit(big_int_to_scalar(vi_val[i].clone().unwrap()), Scalar::random(&mut blinding_rng));
                vi.push(var);
                vi_com.push(com);
                let (com, var) = prover.commit(big_int_to_scalar(vi_mod_val[i].clone().unwrap()), Scalar::random(&mut blinding_rng));
                vi_mod.push(var);
                vi_mod_com.push(com);
            }

            ExtendedProofOfMod::gadget(&mut prover, &a, &a_val, &a_mod, &a_mod_val, &vi, &vi_val, &vi_mod, &vi_mod_val, p, &p0, v_var)?;
            
            combined_a_mod_com.push(a_mod_com.clone());
            combined_vi_com.push(vi_com.clone());
            combined_vi_mod_com.push(vi_mod_com.clone());
        }

        let proof = prover.prove(&bp_gens)?;

        Ok((ExtendedProofOfMod(proof), s_com, v_com, a_com, combined_a_mod_com, combined_vi_com, combined_vi_mod_com))
    }

    pub fn verify_share<'a, 'b>(
        &self,
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        s_com: CompressedRistretto,
        v_com: &Vec<CompressedRistretto>,
        a_com: &Vec<CompressedRistretto>,
        a_mod_com: &Vec<Vec<CompressedRistretto>>,
        vi_com: &Vec<Vec<CompressedRistretto>>,
        vi_mod_com: &Vec<Vec<CompressedRistretto>>,
        weights: &Vec<BigUint>,
        p0: BigUint,
    ) -> Result<(), R1CSError> {
        transcript.append_message(b"dom-sep", b"AggregatedExtendedProofOfMod");

        let mut verifier = Verifier::new(transcript);

        let s_var = verifier.commit(s_com);

        let mut a = vec![];
        for i in 0..a_com.len() {
            let a_var = verifier.commit(a_com[i].clone());
            a.push(a_var);
        }
        verifier.constrain(s_var - a[0]);

        for p_index in 0..weights.len() {
            let v_var = verifier.commit(v_com[p_index]);
            
            let mut a_mod = vec![];

            let mut vi = vec![];
            let mut vi_mod = vec![];

            for i in 0..a_mod_com[p_index].len() {
                let a_mod_var = verifier.commit(a_mod_com[p_index][i].clone());
                a_mod.push(a_mod_var);
            }

            for i in 0..vi_com[p_index].len() {
                let vi_var = verifier.commit(vi_com[p_index][i].clone());
                vi.push(vi_var);
                let vi_mod_var = verifier.commit(vi_mod_com[p_index][i].clone());
                vi_mod.push(vi_mod_var);
            }

            ExtendedProofOfMod::gadget(&mut verifier, &a, &vec![], &a_mod, &vec![], &vi, &vec![], &vi_mod, &vec![], &weights[p_index], &p0, v_var)?;
        }

        verifier.verify(&self.0, pc_gens, bp_gens)
    }

    pub fn from_bytes(slice: &[u8]) -> ExtendedProofOfMod {
        ExtendedProofOfMod(R1CSProof::from_bytes(slice).unwrap())
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        self.0.to_bytes()
    }
}
