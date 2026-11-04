// Largest element of a nonempty vector.
use vstd::prelude::*;

verus! {

fn max_array(a: &Vec<i32>) -> (m: i32)
    requires
        a.len() > 0,
    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= m,
        exists|i: int| 0 <= i < a.len() && a[i] == m,
{
    a[0]
}

} // verus!
