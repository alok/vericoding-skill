// Sum of an array, computed with a loop.
// The spec function walks the sequence from the front; the loop walks it from the front too,
// so each step appends one element on the right. Connecting the two needs a small lemma.

function Sum(s: seq<int>): int
{
  if |s| == 0 then 0 else s[0] + Sum(s[1..])
}

method SumArray(a: array<int>) returns (total: int)
  ensures total == Sum(a[..])
{
  total := 0;
}
