predicate thereIsNoMatchStartingHere(thestring: string, pattern: string, here : int)
  requires 0 <= here
{
  if(here + |pattern| > |thestring|) then true else thestring[here .. here + |pattern|] != pattern
}

method stringMatch(thestring: string, pattern: string) returns (start : int) 
  requires |pattern| > 0
  ensures start == -1 || (0 <= start && start + |pattern| <= |thestring|)
  ensures start == -1 <==> (forall i :: 0 <= i <= |thestring| - |pattern| ==> thereIsNoMatchStartingHere(thestring, pattern, i))
{
    if(|pattern| > |thestring|) {
		return -1;
    }
    var i : int;
    var j : int;
	i := 0;
	j := 0;

	while (i < |thestring| && j < |pattern|)
	decreases  |thestring| - i + j,  |pattern| - j
	invariant 0 <= i <= |thestring|
	invariant 0 <= j <= |pattern|
	invariant forall k :: 0 <= k < j ==> thestring[i - j + k] == pattern[k]
	invariant thereIsNoMatchStartingHere(thestring, pattern, i - j) ==> j < |pattern|
	invariant forall h :: 0 <= h < i - j ==> thereIsNoMatchStartingHere(thestring, pattern, h)
	{
		if (thestring[i] == pattern[j]) {
			j := j + 1;
		} else {
			i := i - j;
			j := 0;
		}
		i := i + 1;
	}
		
	if(j == |pattern|) {
		return i - j;
    }

	return -1;	
}