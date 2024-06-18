use std::array::from_fn;

use bulletproofs::r1cs::*;
use curve25519_dalek::{digest::typenum::bit, ristretto::CompressedRistretto, scalar::Scalar};
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use rand::thread_rng;

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

fn main() {
    println!("Hello, world!");
    let n: usize = 7;
    let v: u64 = 42;
    let u: u64 = 100;

    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(
        (2 * (n+1)).next_power_of_two(),
        1);
    
    println!("Creating range proof for {}", v);
    let (proof, v_com) = {
        let mut prover_transcript = Transcript::new(b"RangeProofExample");
        RangeProof::prove(&pc_gens, &bp_gens, &mut prover_transcript, v, u, n).unwrap()
    };

    println!("Verifying proof for commitment");
    let mut verifier_transcript = Transcript::new(b"RangeProofExample");

    if let Err(e) = proof.verify(
        &pc_gens, &bp_gens, &mut verifier_transcript, v_com, u, n) {
        println!("Failed to verify proof: {:?}", e)
    }
    else {
        println!("Proof verified!");
    }
}
