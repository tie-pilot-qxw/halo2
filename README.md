# halo2 GPU Accelerated [![Crates.io](https://img.shields.io/crates/v/halo2.svg)](https://crates.io/crates/halo2) #

Halo2 Protocol with proof generation accelerated.

## Protocol [Documentation](https://privacy-scaling-explorations.github.io/halo2/halo2_proofs)

For experimental features `privacy-scaling-explorations/halo2` fork adds, please refer to [`experimental-features.md`](./book/src/user/experimental-features.md).

## Minimum Supported Rust Version

Requires Rust nightly later then 2025-09-08 due to some unstable features used in debugging components.

## Dependencies Not Managed by Cargo

Cargo is powerful, but not omnipotent.

First, we need CUDA Toolkit later then 12.8.
Perhaps a previous version would work, but we didn't check that.

Secondly, most of the CUDA compilation is managed by [`xmake`](https://xmake.io).
Follow the instructions on its homepage and have the `xmake` binary available on `PATH`.

## Usage

First clone this repository and checkout the submodule `zkpoly-compiler`:
```bash
git clone <this repository>
git submodule update --init
```

Then, point your dependency of `halo2_proofs` in your Cargo.toml to this repository:
```toml
[dependencies]
halo2_proofs = { path = <path to this repository>/halo2_proofs }
```

However, to wield the power of GPU acceleration, some modifications to your original
calls of `create_proof` must be made.
Specifically, you need to replace it with `halo2_proofs::plonk::jit::create_proof_gpu`,
passing in an unique identifier for each of your circuit.
The identifier is for memorizing compilation artifects when you are creating proofs for the same circuit
on different inputs (or instances, if you prefer Halo2 terms),
and it is necessary because there is no guarantee that we can tell different circuits just from their type name.

For details on how to use the `halo2_proofs::plonk::jit` module, checkout its documention by running
```bash
cd halo2_proofs
cargo doc --open
```

and navigate to the `jit` module.

Finally, remember to set `ZKPOLY_COMPILER_PROJECT_ROOT` to `<path to this repository>/zkpoly-compiler`
since it contains some CUDA code that needs to be compiled during runtime.

## Credits

Some code for computing prime field arithmetics were taken from 
[icicle](https://github.com/ingonyama-zk/icicle/)
and [sppark](https://github.com/supranational/sppark).

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
