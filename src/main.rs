use std::array::from_fn;

use bulletproofs::r1cs::*;
use curve25519_dalek::{digest::typenum::bit, ristretto::CompressedRistretto, scalar::Scalar};
use bulletproofs::{BulletproofGens, PedersenGens};
use merlin::Transcript;
use rand::thread_rng;

extern crate bulletproofs;

// Range proof gadget
struct RangeProof(R1CSProof);

impl RangeProof{
    fn gadget<CS: ConstraintSystem, const N: usize>(
        cs: &mut CS,
        v: Variable,
        a: [Variable; N],
        b: [Variable; N],
    ) -> Result<(), R1CSError> {
        // Constraint 1: v = a[0] + 2*a[1] + 4*a[2] + ... + 2^(N-1)*a[N-1]
        let two = Scalar::from(2u64);
        let a_val = (0..N).rev().fold(
            LinearCombination::from(Scalar::ZERO),
            |prev_out, i| {
            prev_out * two + LinearCombination::from(a[i])
        });
        cs.constrain(v - a_val);

        // Constraint 2: a[i] * b[i] = 0 for all i
        // Constraint 3: a[i] - b[i] - 1 = 0 for all i
        for i in 0..N {
            let (_, _, m_out) = cs.multiply(a[i].into(), b[i].into());
            cs.constrain(m_out.into());
            cs.constrain(a[i] - b[i] - Scalar::ONE);
        }

        Ok(())
    }
}

fn bit_decomp<const N: usize>(v: u64) -> ([Scalar; N], [Scalar; N]) {
    let bits = from_fn(|i| Scalar::from((v >> i) & 1));
    let comp = from_fn(|i| bits[i] - Scalar::ONE);
    (bits, comp)
}

use std::fmt::Debug;
fn unzip_array<T1:Clone + Debug, T2:Clone + Debug, const N: usize>(a:[(T1, T2); N]) -> ([T1; N], [T2; N]) {
    let (a1, a2): (Vec<_>, Vec<_>) = a.iter().cloned().unzip();
    (a1.try_into().unwrap(), a2.try_into().unwrap())
}

impl RangeProof {
    pub fn prove<'a, 'b, const N: usize>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        v: u64,
    ) -> Result<(RangeProof, CompressedRistretto, [CompressedRistretto; N], [CompressedRistretto; N]), R1CSError> {
        transcript.append_message(b"dom-sep", b"RangeProof");

        let mut prover = Prover::new(&pc_gens, transcript);

        // Should probably accept these as inputs, but for now generate as needed
        let mut blinding_rng = rand::thread_rng();

        let (v_com, v_var)
            = prover.commit(Scalar::from(v), Scalar::random(&mut blinding_rng));

        let (a_vals, b_vals) = bit_decomp::<N>(v);

        let (a_coms, a_vars)
            = unzip_array(
                from_fn(|i| prover.commit(a_vals[i],
                    Scalar::random(&mut blinding_rng))));

        let (b_coms, b_vars)
            = unzip_array(
                from_fn(|i| prover.commit(b_vals[i],
                    Scalar::random(&mut blinding_rng))));

        RangeProof::gadget(&mut prover, v_var, a_vars, b_vars)?;

        let proof = prover.prove(&bp_gens)?;

        Ok((RangeProof(proof), v_com, a_coms, b_coms))
    }
}

impl RangeProof {
    pub fn verify<'a, 'b, const N: usize>(
        &self,
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        v_com: CompressedRistretto,
        a_coms: [CompressedRistretto; N],
        b_coms: [CompressedRistretto; N],
    ) -> Result<(), R1CSError> {
        transcript.append_message(b"dom-sep", b"RangeProof");

        let mut verifier = Verifier::new(transcript);

        let v_var = verifier.commit(v_com);

        let a_vars: [Variable; N] = from_fn(|i| verifier.commit(a_coms[i]));
        let b_vars: [Variable; N] = from_fn(|i| verifier.commit(b_coms[i]));

        RangeProof::gadget(&mut verifier, v_var, a_vars, b_vars)?;

        verifier.verify(&self.0, pc_gens, bp_gens)?;
        Ok(())
    }
}

fn main() {
    println!("Hello, world!");
    let N: usize = 64;
    let v: u64 = 42;

    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(
        (2 * (N+1)).next_power_of_two(),
        1);
    
    println!("Creating range proof for {}", v);
    let (proof, v_com, a_coms, b_coms) = {
        let mut prover_transcript = Transcript::new(b"RangeProofExample");
        RangeProof::prove::<64>(&pc_gens, &bp_gens, &mut prover_transcript, v).unwrap()
    };

    println!("Verifying proof for commitment");
    let mut verifier_transcript = Transcript::new(b"RangeProofExample");
    assert!(     
        proof
            .verify(&pc_gens, &bp_gens, &mut verifier_transcript, v_com, a_coms, b_coms)
            .is_ok()
    );
}
