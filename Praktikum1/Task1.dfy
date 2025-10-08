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

method TestMaxSum()
{
    var inputX, inputY := 4235, 5;
    var s, m := MaxSum(inputX, inputY);
    assert(s == inputX + inputY);
    assert(m == inputX);
}