method RequiredStudyTime(c:nat) returns (hours: nat)

method Outer(a: nat)
{
    if a != 0 {
        var b := RequiredStudyTime(a-1);
        Inner(a, b);
    }
}

method Inner(a: nat, b: nat)
requires 1 <= a
{
    if b==0 {
        Outer(a-1);
    } else {
        Inner(a, b-1);
    }
}


/*method RequiredStudyTime'(c:nat) returns (hours: nat)

method Outer'(a: nat)
decreases a
{
    if a != 0 {
        var b := RequiredStudyTime'(a-1);
        Inner'(a-1, b);
    }
}

method Inner'(a: nat, b: nat)
requires 1 <= a
decreases b
{
    if b==0 {
        Outer'(a);
    } else {
        Inner'(a, b-1);
    }
}*/
