method Triple(x: int) returns (r: int)
ensures r == 3 * x
{
    r := 3*x;
}

method Triple'(x: int) returns (r: int)
requires x % 2 == 0
ensures (r + 3*x) / 2 == 3*x
ensures r % 2 == (x * 3) % 2
{
    r := 3 * x + (x % 2);
}

method TestTrippleEquals(x: int)
requires x % 2 == 0
{
    var r1 := Triple(x);
    var r2 := Triple'(x);
    assert r1 == r2;
}