//! Various ways to traverse commit graphs and trees with implementations as iterator
#![deny(missing_docs, rust_2018_idioms)]
#![forbid(unsafe_code)]

/// Commit traversal
pub mod commit;

/// Topological commit traversal
pub mod topo;

/// Tree traversal
pub mod tree;
