procedure Compute(x: int) returns (y: int)
{
    y := 5 * x + 3;
    assert (x + y) == ((6 * x) + 3);
}