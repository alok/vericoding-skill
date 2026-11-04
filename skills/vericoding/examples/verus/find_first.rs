// Index of the first occurrence of x, if any.
use vstd::prelude::*;

verus! {

fn find_first(v: &Vec<i32>, x: i32) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => i < v.len() && v[i as int] == x && forall|j: int| 0 <= j < i ==> v[j] != x,
            None => forall|j: int| 0 <= j < v.len() ==> v[j] != x,
        },
{
    None
}

} // verus!
