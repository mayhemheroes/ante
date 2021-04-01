#[derive(Copy, Clone)]
pub enum AllocationCount {
    /// This ref is never allocated to.
    /// This is common in functions taking refs as parameters without
    /// returning them or unifying them with other refs.
    Zero,

    /// This ref is allocated to a known upper-bound number of times.
    /// I.e. there are no loops or recursive calls between each allocation
    /// and the furthest stack frame the variables may reach.
    /// In practice this tends to be a low value (almost always 1).
    /// Refs with a known number of allocations can be optimized during
    /// codegen to be allocated on the stack.
    NonZero(u32),

    /// This ref is allocated to an unknown (non-zero) number of times.
    /// This may happen if we allocate values to the same ref in a loop
    /// or recursive function call where the refs escape into a lower
    /// scope than the loop/call.
    Unknown,
}

impl AllocationCount {
    pub fn increment(self) -> AllocationCount {
        match self {
            AllocationCount::Zero => AllocationCount::NonZero(1),
            AllocationCount::NonZero(n) => AllocationCount::NonZero(n + 1),
            AllocationCount::Unknown => AllocationCount::Unknown,
        }
    }
}
