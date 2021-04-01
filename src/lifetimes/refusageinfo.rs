use crate::lifetimes::allocationcount::AllocationCount;
use crate::lifetimes::{ LifetimeVariableId, StackFrameIndex };

pub struct RefUsageInfo {
    /// The lifetime field is mostly for use in visited_definitions so that
    /// callsites can find which LifetimeVariableId at the callsite to unify
    /// with these LifetimeVariableIds from the function definition.
    /// The StackFrameIndex is a better indicator of the actual lifetime of
    /// the variable.
    lifetime: LifetimeVariableId,
    lowest_stackframe: StackFrameIndex,

    /// TODO: Caching AllocationCount for each function argument is likely unsound
    /// in the presence of traits and lambdas. The two problematics cases are:
    /// ```ante
    /// impl Cast a (ref a) with cast a = &a
    ///
    /// foo a = cast a
    /// ```
    /// where no instances of `&` would be found in `foo` and thus it would not
    /// increase the AllocationCount of a, making the stack optimization unsound.
    /// The other case is:
    /// ```ante
    /// alloc x = &x
    ///
    /// foo f x =
    ///     for _ in 0..10 do f x
    ///
    /// foo alloc 1
    /// ```
    /// Where the AllocationCount should be Unknown since it is allocated to in a
    /// loop but may erroneously be 1 since we do not see the definition of `f` while
    /// we are analyzing `foo`.
    allocation_count: AllocationCount,
}

impl RefUsageInfo {
    pub fn new(lifetime_id: LifetimeVariableId, level: StackFrameIndex) -> RefUsageInfo {
        RefUsageInfo {
            lowest_stackframe: level,
            lifetime: lifetime_id,
            allocation_count: AllocationCount::Zero,
        }
    }

    pub fn increment_allocation_count(&mut self) {
        self.allocation_count = self.allocation_count.increment();
    }
}
