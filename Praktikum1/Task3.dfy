method Triple(x: int) returns (r: int)
ensures r == 3 * x
{
    r := 3*x;
}

method Triple'(x: int) returns (r: int)
ensures (r + 3*x) / 2 == 3*x
ensures r <= 3*x
{
    //r := 3 * x + (x % 2);
    r := 3*x;
}

method TestTrippleEquals(x: int)
{
    var r1 := Triple(x);
    var r2 := Triple'(x);
    assert r1 == r2;
}