method isPalindromMethod(myString: string) returns (isPalindrom: bool)
requires |myString| > 0
ensures isPalindrom == (forall lo :: 0 <= lo < |myString| ==> myString[lo] == myString[|myString| - 1 - lo])
{
    var lo := 0;
    var hi := |myString| - 1;
    isPalindrom := true;

    while (lo < hi)
        invariant 0 <= lo <= hi + 1 <= |myString|
        invariant lo + hi == |myString| - 1
        invariant isPalindrom
        invariant isPalindrom ==> (forall i :: 0 <= i < lo ==> myString[i] == myString[|myString| - 1 - i])
        decreases hi - lo
    {
        if myString[lo] != myString[hi] {
            isPalindrom := false;
            return;
        }
        lo := lo + 1;
        hi := hi - 1;
    }

}
