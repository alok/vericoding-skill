// Sum of an array, computed with a loop.
// The spec function walks the sequence from the front; the loop walks it from the front too,
// so each step appends one element on the right. Connecting the two needs a small lemma.

function Sum(s: seq<int>): int
{
  if |s| == 0 then 0 else s[0] + Sum(s[1..])
}

// Helper: summing s + [x] adds x. Proved by induction on s.
lemma SumAppend(s: seq<int>, x: int)
  ensures Sum(s + [x]) == Sum(s) + x
{
  if |s| == 0 {
    assert s + [x] == [x];
  } else {
    assert (s + [x])[1..] == s[1..] + [x];
    SumAppend(s[1..], x);
  }
}

method SumArray(a: array<int>) returns (total: int)
  ensures total == Sum(a[..])
{
  total := 0;
  var k := 0;
  while k < a.Length
    invariant 0 <= k <= a.Length
    invariant total == Sum(a[..k])
  {
    assert a[..k + 1] == a[..k] + [a[k]];
    SumAppend(a[..k], a[k]);
    total := total + a[k];
    k := k + 1;
  }
  assert a[..a.Length] == a[..];
}
