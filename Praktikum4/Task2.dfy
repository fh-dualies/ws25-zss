method maximum(myArray : array<int>) returns (m : int)
requires myArray.Length > 0
ensures forall i :: 0 <= i < myArray.Length ==> m >= myArray[i]
{
    var i := 0;
    m := myArray[0];
    while (i < myArray.Length) 
    invariant 0 <= i <= myArray.Length
    invariant forall k :: 0 <= k < i ==> m >= myArray[k]
    {
        if (myArray[i] > m) {
            m := myArray[i];
        }
        i := i + 1;
    }
}
