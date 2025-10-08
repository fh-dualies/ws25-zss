method Triple(x: int) returns (r: int)
ensures r == 3 * x
{
    r := 3*x;
}

method Triple'(x: int) returns (r: int)
ensures (r + 3*x) / 2 == 3*x
{
    r := 3 * x + (x % 2);
}
