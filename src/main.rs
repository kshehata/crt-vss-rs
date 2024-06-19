use bulletproofs::r1cs::*;
use curve25519_dalek::{ristretto::CompressedRistretto, scalar::Scalar};
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;

extern crate bulletproofs;

// Add equations to constrain a value to [0, 2^n).
pub fn add_range_constraints<CS: ConstraintSystem>(
    cs: &mut CS,
    // Variable of value to be constrained
    mut v: LinearCombination,
    // If set, what to assign the wires to.
    v_val: Option<u64>,
    // Bit size of value
    n: usize,
) -> Result<(), R1CSError> {
    let mut pow_2 = Scalar::ONE;
    for i in 0..n {
        // Add constraints for bit i
        let (a, b, o) = cs.allocate_multiplier(
            v_val.map(|x| {
                let bit: u64 = (x >> i) & 1;
                (bit.into(), (1 - bit).into())
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
        v: u64,
        u: u64,
        n: usize,
    ) -> Result<(RangeProof, CompressedRistretto), R1CSError> {
        transcript.append_message(b"dom-sep", b"RangeProof");

        let mut prover = Prover::new(&pc_gens, transcript);

        // Should probably accept these as inputs, but for now generate as needed
        let mut blinding_rng = rand::thread_rng();

        let (v_com, v_var)
            = prover.commit(Scalar::from(v), Scalar::random(&mut blinding_rng));

        assert!(add_range_constraints(&mut prover, v_var.into(), Some(v), n).is_ok());
        assert!(add_range_constraints(&mut prover, LinearCombination::from(u) - v_var, Some(u-v), n).is_ok());

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
        u: u64,
        n: usize,
    ) -> Result<(), R1CSError> {
        transcript.append_message(b"dom-sep", b"RangeProof");

        let mut verifier = Verifier::new(transcript);

        let v_var = verifier.commit(v_com);

        assert!(add_range_constraints(&mut verifier, v_var.into(), None, n).is_ok());
        assert!(add_range_constraints(&mut verifier, LinearCombination::from(u) - v_var, None, n).is_ok());

        verifier.verify(&self.0, pc_gens, bp_gens)
    }
}

pub fn add_bit_constraints<CS: RandomizedConstraintSystem>(
    cs: &mut CS,
    mut v: LinearCombination,
    v_val: Option<u64>,
    n: usize,
    z: Scalar,
) -> Result<LinearCombination, R1CSError> {
    let v_in_range = v_val.map(|x| x < (1 << n)).unwrap_or(false);
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
            v_val.map(|x| {
                if v_in_range {
                    let bit: u64 = (x >> i) & 1;
                    (bit.into(), (1 - bit).into())
                } else if i == 0 {
                    (x.into(), Scalar::ZERO.into())
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
    v1_val: Option<u64>,
    v2_val: Option<u64>,
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
        v1: u64,
        v2: u64,
        n1: usize,
        n2: usize,
    ) -> Result<(DisjunctionOfRanges, CompressedRistretto, CompressedRistretto), R1CSError> {
        transcript.append_message(b"dom-sep", b"DisjunctionOfRanges");

        let mut prover = Prover::new(&pc_gens, transcript);

        // Should probably accept these as inputs, but for now generate as needed
        let mut blinding_rng = rand::thread_rng();

        let (v1_com, v1_var)
            = prover.commit(Scalar::from(v1), Scalar::random(&mut blinding_rng));
        let (v2_com, v2_var)
            = prover.commit(Scalar::from(v2), Scalar::random(&mut blinding_rng));

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

fn main() {
    println!("Hello, world!");
    let (v1, n1) = (128u64, 8usize);
    let (v2, n2) = (42u64, 5usize);

    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(
        (2 * (n1 + n2 + 1)).next_power_of_two(),
        1);
    
    println!("Creating range disjunction proof for {} in {} bits and {} in {} bits", v1, n1, v2, n2);
    let (proof, v1_com, v2_com) = {
        let mut prover_transcript = Transcript::new(b"RangeProofExample");
        DisjunctionOfRanges::prove(&pc_gens, &bp_gens, &mut prover_transcript, v1, v2, n1, n2).unwrap()
    };

    println!("Verifying proof for commitment");
    let mut verifier_transcript = Transcript::new(b"RangeProofExample");

    if let Err(e) = proof.verify(
        &pc_gens, &bp_gens, &mut verifier_transcript, v1_com, v2_com, n1, n2) {
        println!("Failed to verify proof: {:?}", e)
    }
    else {
        println!("Proof verified!");
    }
}
