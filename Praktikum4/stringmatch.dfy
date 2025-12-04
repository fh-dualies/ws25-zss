predicate thereIsNoMatchStartingHere(thestring: string, pattern: string, here : int)
  requires 0 <= here
{
  if(here + |pattern| > |thestring|) then true else thestring[here .. here + |pattern|] != pattern
}

method stringMatch(thestring: string, pattern: string) returns (start : int) 
/**TODO */
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
	/**TODO */
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