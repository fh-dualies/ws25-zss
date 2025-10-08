method MaxSum(x: int, y: int) returns (s: int, m: int)
ensures s == x + y
ensures (m == x || m == y) && x <= m && y <= m
{
   s := x + y;

   if x < y {
    m := y;
   } else {
    m := x;
   }
}

method ReconstructFromMaxSum(s: int, m: int) returns(x: int, y: int)
requires s <= 2*m
ensures s == x + y
ensures x <= m && y <= m
ensures y == m && x == s - m
{
    x := s - m;
    y :=  m;
}

method TestReconstructFromMaxSum(x: int, y: int)
{
    var s, m := MaxSum(x, y);
    var xx, yy := ReconstructFromMaxSum(s, m);
    assert(xx == x && yy == y) || (xx == y && yy == x);
}