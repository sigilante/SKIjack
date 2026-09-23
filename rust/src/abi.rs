//! What is normative, gathered in one place.

/// The instruction set.
pub const ISA: [&str; 3] = ["S", "K", "I"];

/// Tier 1: closed terms over the ISA a program may name directly.
pub const TIER1_NAMES: [&str; 4] = ["B", "C", "W", "Y"];

pub fn is_isa(name: &str) -> bool {
    ISA.contains(&name)
}

pub fn is_tier1(name: &str) -> bool {
    TIER1_NAMES.contains(&name)
}
