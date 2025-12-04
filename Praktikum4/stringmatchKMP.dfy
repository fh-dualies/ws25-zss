predicate isMatch(mystringOne: string, offset : int, length : int, mystringTwo : string) 
requires offset >= 0
requires length <= offset
requires offset <= |mystringOne|
requires length <= |mystringTwo|
{
	forall k :: (0 <= k < length) ==> mystringOne[offset - length + k] == mystringTwo[k]
}

method analysePrefix(pattern: string) returns (ptable : array<int>)
ensures ptable.Length == |pattern|
ensures forall k :: (0 <= k < |pattern|) ==> (ptable[k] < k)
ensures forall k :: (0 < k < |pattern|) ==> ptable[k] >= 0
ensures forall j :: (0 <= j < |pattern|) ==> isMatch(pattern, j, ptable[j], pattern)
{
		if(|pattern| == 0) {
			return new int[0];
		}
		var N := new int[|pattern|];
		var i : int;
		var j : int;
		i := 0;
		j := -1;
		N[0] := -1;
		
		while(i < |pattern| - 1)
		{
			while(j >= 0 && pattern[i] != pattern[j]) 
			{				
				j := N[j];	
			}
			
			i := i + 1;
			j := j + 1;
			
			N[i] := j;
		}
		return N;
	}


method stringMatch(thestring: string, pattern: string) returns (start : int) 
{
    if(|pattern| > |thestring|) {
			return -1;
    }
    var i : int;
    var j : int;
	i := 0;
	j := 0;
	var N := analysePrefix(pattern);

	while (i < |thestring| && j < |pattern|)
    {
			if (thestring[i] == pattern[j]) {
				j := j + 1;
			} else if (j > 0) {
				j := N[j];
				i := i - 1;
			}
			i := i + 1;
	}
		
		if(j == |pattern|) {
			return i - j;
        }
		return -1;	
}