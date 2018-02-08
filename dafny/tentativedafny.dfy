    predicate sorted(a:array<int>, min:int, max:int)
    requires a != null;
    requires 0<= min <= max <= a.Length;
    reads a;
    {
      forall j, k :: min <= j < k < max ==> a[j] <= a[k]
    }

	predicate sorted1(a:array<int>, min:int, max:int)
    requires a != null;
    requires 0<= min <= max <= a.Length;
    reads a;
    {
      forall j, k :: min <= j < k < max ==> a[j] <= a[k]
    }
    
    predicate sortedSeq(a:seq<int>)
    {
      forall j, k :: 0 <= j < k < |a| ==> a[j] <= a[k]
    }

method InsertionSort ( a:array<int> )
		requires a != null && a.Length >= 1 
		modifies a 
		ensures sorted(a,0, a.Length)
	{    var i ,j, k , t:= 1,0, 0,0;	      
		  while ( i < a.Length )
		  invariant 0 <= i <= a.Length;
		  invariant sorted(a,0, i);
		  {
		    j,k := i, a[i];
			while ( j > 0  && a[j-1] > k ) 
			invariant 0 <= j <= i
			invariant sorted1 (a, 0, j)
			invariant sorted1 (a,j, i)
			invariant forall k1, k2 :: 0 <= k1 <= k2 <= i ==> k1 != j ==> k2 != j ==> a[k1] <= a[k2]
			invariant forall l :: j+1 <= l <= i ==> k <= a[l]
			{
			//t := a[j];
			a[j] := a[j-1];
            //a[j-1] := t;
			j := j-1;
			}
			a[j] := k;
			i := i +1;
		  }

		  
	}
