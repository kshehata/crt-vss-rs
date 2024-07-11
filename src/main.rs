use bulletproofs::{BulletproofGens, PedersenGens};
use crt_vss_rs::ExtendedProofOfMod;
use merlin::Transcript;
use num_bigint::BigUint;
use num_primes::Generator;
use std::fs::OpenOptions;

fn get_prime_for_weight(n: usize) -> BigUint {
    BigUint::from_bytes_le(Generator::new_prime(n).to_bytes_le().as_slice())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let p0: BigUint = (BigUint::from(1u64) << 252) + BigUint::from(27742317777372353535851937790883648493u128);
    // The value of p0 is the prime order defined by the bulletproof library.

    // Test secret sharing
    let p = vec![get_prime_for_weight(128),
                               get_prime_for_weight(16),
                               get_prime_for_weight(224),
                               get_prime_for_weight(96),
                               get_prime_for_weight(32),
                               get_prime_for_weight(192),
                               get_prime_for_weight(200),
                               get_prime_for_weight(136)];
    
    let s = BigUint::from_bytes_le(&[209, 91, 84, 175, 236, 117, 121, 113, 47, 98, 118, 129, 54, 83, 102, 3, 97, 11, 17, 9, 
                                                    121, 11, 189, 13, 7, 53, 191]);

    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(
        (512 * (256usize)).next_power_of_two(),
        1);

    use std::time::Instant;
    let prover_start = Instant::now();
    let (xproof, s_com, v_com, a_com, a_mod_com, vi_com, vi_mod_com) = {
        let mut prover_transcript = Transcript::new(b"ExtendedProofOfModVSSExample");
        ExtendedProofOfMod::share(&pc_gens, &bp_gens, &mut prover_transcript, s.clone(), &p, p0.clone()).unwrap()
    };
    println!("Extended proof created for secret sharing in {:.2?}", prover_start.elapsed());

    let proof_filename = "export_share_proof.json";
    let commitment_filename = "export_commitment.json";

    let mut file = OpenOptions::new()
        .create(true)
        .truncate(true)
        .write(true)
        .read(true)
        .open(proof_filename)?;

    serde_json::to_writer(&mut file, &xproof.to_bytes())?;

    file = OpenOptions::new()
        .create(true)
        .truncate(true)
        .write(true)
        .read(true)
        .open(commitment_filename)?;

    serde_json::to_writer(&mut file, &s_com)?;
    serde_json::to_writer(&mut file, &v_com)?;
    serde_json::to_writer(&mut file, &a_com)?;
    serde_json::to_writer(&mut file, &a_mod_com)?;
    serde_json::to_writer(&mut file, &vi_com)?;
    serde_json::to_writer(&mut file, &vi_mod_com)?;

    let xproof_read_bytes: Vec<u8> = serde_json::from_reader(OpenOptions::new().read(true).open(proof_filename)?)?;
    let xproof_from_file: ExtendedProofOfMod = ExtendedProofOfMod::from_bytes(&xproof_read_bytes);
    assert!(&xproof.to_bytes() == &xproof_from_file.to_bytes());
    println!("Read extended proof for VSS from file.");

    let mut verifier_transcript = Transcript::new(b"ExtendedProofOfModVSSExample");
    let verify_start = Instant::now();
    if let Err(e) = xproof_from_file.verify_share(
        &pc_gens, &bp_gens, &mut verifier_transcript, s_com.clone(), &v_com, &a_com, &a_mod_com, &vi_com, &vi_mod_com, &p, p0.clone()) {
        println!("Failed to verify proof: {:?}", e)
    }
    else {
        println!("VSS Extended proof verified!");
    }
    println!("Proof verified in {:.2?}", verify_start.elapsed());

    Ok(())
}
