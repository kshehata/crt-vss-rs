use std::convert::TryInto;
use num_bigint::BigUint;
use bulletproofs::r1cs::*;
use curve25519_dalek::{ristretto::CompressedRistretto, scalar::Scalar};
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;

extern crate bulletproofs;

pub fn big_int_to_scalar (bint: BigUint) -> Scalar {
    let mut bits = bint.to_bytes_le();
    assert!(bits.len() <= 32);
    while bits.len() < 32 {
        bits.push(0);
    }
    Scalar::from_bytes_mod_order(bits.try_into().unwrap())
}

pub fn scalar_to_big_int (scalar: Scalar) -> BigUint {
    BigUint::from_bytes_le(scalar.as_bytes())
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
            = prover.commit(Scalar::from(big_int_to_scalar(v1.clone())), Scalar::random(&mut blinding_rng));
        let (v2_com, v2_var)
            = prover.commit(Scalar::from(big_int_to_scalar(v2.clone())), Scalar::random(&mut blinding_rng));

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
struct ProofOfMod(R1CSProof);

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
        let k = cs.allocate(k_val.as_ref().map(|x| Scalar::from(big_int_to_scalar(x.clone())))).unwrap();

        // Fundamental constraint for proof of mod
        cs.constrain(v + k * big_int_to_scalar(p.clone()) - s);

        add_range_constraints(cs, v.into(), v_val.clone(), n1)?;
        add_range_constraints(cs, k.into(), k_val.clone(), n2)?;
        add_range_constraints(cs, big_int_to_scalar(&p - &big_one) - v, v_val.as_ref().map(|x| &p - x - &big_one), n1)?;
        add_range_constraints(cs, Scalar::from(big_int_to_scalar(q.clone())) - k, k_val.as_ref().map(|x| &q - x), n2)?;
        add_range_disjunction(cs,
            big_int_to_scalar(&t - &big_one) - v,
            big_int_to_scalar(&q - &big_one) - k,
            v_val.as_ref().map(|x| &t - &big_one - x),
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
            = prover.commit(Scalar::from(big_int_to_scalar(v.clone())), Scalar::random(&mut blinding_rng));
        let (s_com, s_var)
            = prover.commit(Scalar::from(big_int_to_scalar(s.clone())), Scalar::random(&mut blinding_rng));

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
fn main() {
    println!("Hello, world!");
    // let bint = BigUint::from_bytes_le(&[6, 1, 4, 5, 6, 7, 8, 2]);
    // let sca = big_int_to_scalar(bint.clone());
    // let bint_ret = scalar_to_big_int(sca.clone());
    // let sca_from_num = Scalar::from(146374710324887814u64);
    // println!("Finished conversion example. Big int is: {:?}, big int converted back is: {:?}, scalar is: {:?}, scalar from num is: {:?}", bint, bint_ret, sca, sca_from_num);
    let (p, p0) = (BigUint::from_bytes_le(&[6, 1, 4, 5, 6, 7, 8, 2]), BigUint::from_bytes_le(&[6, 1, 4, 3, 1, 4, 3, 5, 6, 7, 8, 2]));
    let s = BigUint::from_bytes_le(&[3, 1, 4, 5, 6, 7, 1, 3, 4, 5, 8, 2]);
    let (v, k) = (&s % &p, &s / &p);
    // let (v, k) = (5u64, 28u64);

    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(
        (2 * (129usize)).next_power_of_two(),
        1);
    
    println!("Creating a proof of mod for {} (in {}) = {} + {} * {}", &s, &p0, &v, &k, &p);
    let (proof, v_com, s_com) = {
        let mut prover_transcript = Transcript::new(b"ProofOfModExample");
        ProofOfMod::prove(&pc_gens, &bp_gens, &mut prover_transcript, v.clone(), s.clone(), k.clone(), p.clone(), p0.clone()).unwrap()
    };

    println!("Verifying proof for commitment");
    let mut verifier_transcript = Transcript::new(b"ProofOfModExample");

    if let Err(e) = proof.verify(
        &pc_gens, &bp_gens, &mut verifier_transcript, v_com.clone(), s_com.clone(), p.clone(), p0.clone()) {
        println!("Failed to verify proof: {:?}", e)
    }
    else {
        println!("Proof verified!");
    }
}
