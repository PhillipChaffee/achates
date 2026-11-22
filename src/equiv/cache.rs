//! The record of each theorem's search: its outcome and its tries.

use serde::Serialize;

/// One try, as recorded.
#[derive(Debug, Clone, Serialize, PartialEq)]
pub(crate) struct TryRecord {
    pub(crate) tier: usize,
    /// The `maxHeartbeats` it ran with.
    pub(crate) budget: u64,
    /// What it used, when Lean reported it.
    pub(crate) heartbeats: Option<u64>,
    pub(crate) seconds: f64,
    /// `proved`, or what the failure was.
    pub(crate) result: String,
    /// The first error's first lines, when it failed.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) first_error: Option<String>,
}

/// What became of one theorem.
#[derive(Debug, Clone, Serialize, PartialEq)]
pub(crate) struct Entry {
    /// The tier that proved it, if one did.
    pub(crate) proved: Option<usize>,
    /// Why it is open, when it is.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) reason: Option<String>,
    pub(crate) tries: Vec<TryRecord>,
    /// The `#print axioms` message of the proof.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) axioms: Option<String>,
}
