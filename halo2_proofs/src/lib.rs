//! # halo2_proofs

#![cfg_attr(docsrs, feature(doc_cfg))]
// The actual lints we want to disable.
#![allow(clippy::op_ref, clippy::many_single_char_names)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
// #![deny(missing_docs)]
#![allow(type_alias_bounds)]

pub mod arithmetic;
pub mod circuit;
pub use halo2curves;
mod multicore;
pub mod plonk;
pub mod poly;
pub mod transcript;

pub mod dev;
mod helpers;
pub use helpers::SerdeFormat;

pub mod tracing;

pub use zkpoly_common;
pub use zkpoly_compiler;
pub use zkpoly_cuda_api;
pub use zkpoly_memory_pool;
pub use zkpoly_runtime;
pub use zkpoly_scheduler;
