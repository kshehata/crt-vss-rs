use bulletproofs::{BulletproofGens, PedersenGens};
use crt_vss_rs::{compute_a, ExtendedProofOfMod, ProofOfMod};
use merlin::Transcript;
use num_bigint::BigUint;

use std::fs::OpenOptions;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let p0: BigUint = (BigUint::from(1u64) << 252) + BigUint::from(27742317777372353535851937790883648493u128);
    // // let bint = BigUint::from_bytes_le(&[6, 1, 4, 5, 6, 7, 8, 2]);
    // // let sca = big_int_to_scalar(bint.clone());
    // // let bint_ret = scalar_to_big_int(sca.clone());
    // // let sca_from_num = Scalar::from(146374710324887814u64);
    // // println!("Finished conversion example. Big int is: {:?}, big int converted back is: {:?}, scalar is: {:?}, scalar from num is: {:?}", bint, bint_ret, sca, sca_from_num);
    // let p = BigUint::from_bytes_le(&[6, 1, 4, 5, 6, 7, 8, 2]);
    // let s = BigUint::from_bytes_le(&[3, 1, 4, 5, 6, 7, 1, 3, 4, 5, 8, 2]);
    // let (v, k) = (&s % &p, &s / &p);
    // // let (v, k) = (5u64, 28u64);

    // let pc_gens = PedersenGens::default();
    // let bp_gens = BulletproofGens::new(
    //     (5 * (256usize)).next_power_of_two(),
    //     1);
    
    // println!("Creating a proof of mod for {} (in {}) = {} + {} * {}", &s, &p0, &v, &k, &p);
    // let (proof, v_com, s_com) = {
    //     let mut prover_transcript = Transcript::new(b"ProofOfModExample");
    //     ProofOfMod::prove(&pc_gens, &bp_gens, &mut prover_transcript, v.clone(), s.clone(), k.clone(), p.clone(), p0.clone()).unwrap()
    // };

    // println!("Verifying proof for commitment");
    // let mut verifier_transcript = Transcript::new(b"ProofOfModExample");

    // if let Err(e) = proof.verify(
    //     &pc_gens, &bp_gens, &mut verifier_transcript, v_com.clone(), s_com.clone(), p.clone(), p0.clone()) {
    //     println!("Failed to verify proof: {:?}", e)
    // }
    // else {
    //     println!("Proof verified!");
    // }

    // let p = BigUint::from_bytes_le(&[3, 162, 64, 175, 36, 7, 68, 31, 123, 187, 78, 14, 51, 19, 71, 199, 245, 21, 216, 93, 153, 97, 203, 19]);
    
    // let s = BigUint::from_bytes_le(&[209, 91, 84, 175, 236, 117, 121, 113, 47, 98, 118, 129, 54, 83, 102, 3, 97, 11, 17, 9, 
    //                                                 121, 11, 189, 13, 7, 111, 97, 43, 98, 155, 53, 190, 39, 163, 28, 153, 109, 226, 29]);
    // let v = &s % &p;
    // let a_vals = compute_a(&s, &p0);

    // let pc_gens = PedersenGens::default();
    // let bp_gens = BulletproofGens::new(
    //     (10 * (256usize)).next_power_of_two(),
    //     1);
    // let (xproof, v_com, a_com, a_mod_com, vi_com, vi_mod_com) = {
    //     let mut prover_transcript = Transcript::new(b"ExtendedProofOfModExample");
    //     ExtendedProofOfMod::prove(&pc_gens, &bp_gens, &mut prover_transcript, v.clone(), &a_vals, p.clone(), p0.clone()).unwrap()
    // };
    // println!("Extended proof created.");

    // let filename = "export_proof.json";

    // let mut file = OpenOptions::new()
    //     .create(true)
    //     .truncate(true) // Overwrite existing file
    //     .write(true)
    //     .read(true)
    //     .open(filename)?;

    // serde_json::to_writer(&mut file, &xproof.to_bytes())?;
    // let xproof_read_bytes: Vec<u8> = serde_json::from_reader(OpenOptions::new().read(true).open(filename)?)?;
    // let xproof_from_file: ExtendedProofOfMod = ExtendedProofOfMod::from_bytes(&xproof_read_bytes);
    // assert!(&xproof.to_bytes() == &xproof_from_file.to_bytes());
    // println!("Read extended proof from file.");

    // verifier_transcript = Transcript::new(b"ExtendedProofOfModExample");
    // if let Err(e) = xproof_from_file.verify(
    //     &pc_gens, &bp_gens, &mut verifier_transcript, v_com.clone(), &a_com, &a_mod_com, &vi_com, &vi_mod_com, p.clone(), p0.clone()) {
    //     println!("Failed to verify proof: {:?}", e)
    // }
    // else {
    //     println!("Extended proof verified!");
    // }

    // test sharing
    let p = vec![BigUint::from_bytes_le(&[3, 162, 64, 175, 36, 7, 68, 31, 123, 187, 78, 245, 217, 203, 19]),
                               BigUint::from_bytes_le(&[3, 162, 64, 175, 31, 123, 187, 3, 153, 197, 203, 19]),
                               BigUint::from(23498571298749812u64),
                               BigUint::from_bytes_le(&[3, 36, 7, 68, 31, 123, 187, 78, 245, 21, 216, 203, 19]),
                               BigUint::from_bytes_le(&[3, 162, 64, 175, 36, 7, 68, 31, 123, 187, 78, 245, 217, 203, 19]),
                               BigUint::from_bytes_le(&[3, 162, 64, 175, 31, 123, 187, 3, 153, 197, 203, 19]),
                               BigUint::from(23498571298749812u64),
                               BigUint::from_bytes_le(&[3, 36, 7, 68, 31, 123, 187, 78, 245, 21, 216, 203, 19])];
    
    let s = BigUint::from_bytes_le(&[209, 91, 84, 175, 236, 117, 121, 113, 47, 98, 118, 129, 54, 83, 102, 3, 97, 11, 17, 9, 
                                                    121, 11, 189, 13, 7, 53, 191]);

    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(
        (512 * (256usize)).next_power_of_two(),
        1);
    let (xproof, s_com, v_com, a_com, a_mod_com, vi_com, vi_mod_com) = {
        let mut prover_transcript = Transcript::new(b"ExtendedProofOfModVSSExample");
        ExtendedProofOfMod::share(&pc_gens, &bp_gens, &mut prover_transcript, s.clone(), &p, p0.clone()).unwrap()
    };
    println!("Extended proof created for secret sharing.");

    let filename = "export_share_proof.json";

    let mut file = OpenOptions::new()
        .create(true)
        .truncate(true)
        .write(true)
        .read(true)
        .open(filename)?;

    serde_json::to_writer(&mut file, &xproof.to_bytes())?;
    let xproof_read_bytes: Vec<u8> = serde_json::from_reader(OpenOptions::new().read(true).open(filename)?)?;
    let xproof_from_file: ExtendedProofOfMod = ExtendedProofOfMod::from_bytes(&xproof_read_bytes);
    assert!(&xproof.to_bytes() == &xproof_from_file.to_bytes());
    println!("Read extended proof from file.");

    let mut verifier_transcript = Transcript::new(b"ExtendedProofOfModVSSExample");
    if let Err(e) = xproof_from_file.verify_share(
        &pc_gens, &bp_gens, &mut verifier_transcript, s_com.clone(), &v_com, &a_com, &a_mod_com, &vi_com, &vi_mod_com, &p, p0.clone()) {
        println!("Failed to verify proof: {:?}", e)
    }
    else {
        println!("VSS Extended proof verified!");
    }

    Ok(())
}
