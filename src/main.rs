use bulletproofs::{BulletproofGens, PedersenGens};
use crt_vss_rs::{ExtendedProofOfMod, ProofOfMod};
use merlin::Transcript;
use num_bigint::BigUint;

use std::fs::OpenOptions;

fn main() -> Result<(), Box<dyn std::error::Error>> {
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

    let p = BigUint::from_bytes_le(&[3, 1, 4, 5, 6, 7, 8, 3]);
    let p0 = BigUint::from_bytes_le(&[3, 1, 4, 31, 1, 4, 3, 5, 61, 79, 8, 1, 3, 1, 13, 7, 61, 113]);
    let mut s = BigUint::from_bytes_le(&[3, 1, 4, 5, 6, 7, 121, 3, 4, 54, 83, 2, 3, 7, 11, 17, 9, 1, 11, 1, 13, 7, 111, 97, 43]);
    let v = &s % &p;
    let mut a_vals = vec![];
    a_vals.push(&s % &p0);
    s = &s / &p0;
    while s > BigUint::ZERO {
        a_vals.push(&s % &p0);
        s = &s / &p0;
    }

    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(
        (5 * (256usize)).next_power_of_two(),
        1);
    let (xproof, v_com, a_com, a_mod_com, vi_com, vi_mod_com) = {
        let mut prover_transcript = Transcript::new(b"ExtendedProofOfModExample");
        ExtendedProofOfMod::prove(&pc_gens, &bp_gens, &mut prover_transcript, v.clone(), &a_vals, p.clone(), p0.clone()).unwrap()
    };
    println!("Extended proof created.");

    let filename = "export_proof.json";

    let mut file = OpenOptions::new()
        .create(true)
        .truncate(true) // Overwrite existing file
        .write(true)
        .read(true)
        .open(filename)?;

    serde_json::to_writer(&mut file, &xproof.to_bytes())?;
    let xproof_read_bytes: Vec<u8> = serde_json::from_reader(OpenOptions::new().read(true).open(filename)?)?;
    let xproof_from_file: ExtendedProofOfMod = ExtendedProofOfMod::from_bytes(&xproof_read_bytes);
    assert!(&xproof.to_bytes() == &xproof_from_file.to_bytes());
    println!("Read extended proof from file.");

    verifier_transcript = Transcript::new(b"ExtendedProofOfModExample");
    if let Err(e) = xproof_from_file.verify(
        &pc_gens, &bp_gens, &mut verifier_transcript, v_com.clone(), &a_com, &a_mod_com, &vi_com, &vi_mod_com, p.clone(), p0.clone()) {
        println!("Failed to verify proof: {:?}", e)
    }
    else {
        println!("Extended proof verified!");
    }

    Ok(())
}
