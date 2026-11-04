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
    let mut m = a[0];
    let mut k: usize = 1;
    while k < a.len()
        invariant
            1 <= k <= a.len(),
            forall|i: int| 0 <= i < k ==> a[i] <= m,
            exists|i: int| 0 <= i < k && a[i] == m,
        decreases a.len() - k,
    {
        if a[k] > m {
            m = a[k];
        }
        k += 1;
    }
    m
}

} // verus!
