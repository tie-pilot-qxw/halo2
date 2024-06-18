use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;
use tiny_keccak::Hasher;

pub fn test_rng() -> ChaCha20Rng {
    ChaCha20Rng::seed_from_u64(0xdeadbeef)
}

/// Gets the hex representation of the keccak hash of the input data
pub fn keccak_hex<D: AsRef<[u8]>>(data: D) -> String {
    let mut hash = [0u8; 32];
    let mut hasher = tiny_keccak::Keccak::v256();
    hasher.update(data.as_ref());
    hasher.finalize(&mut hash);
    hex::encode(hash)
}
pub mod display;
