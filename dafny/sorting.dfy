predicate sorted(a: array<int>, i: int)

   requires a != null
   requires 0 <= i <= a.Length
   reads a
{
   forall k, l :: 0 <= k < l < i ==> a[k] <= a[l]
}

predicate sorted1(a:array<int>, min:int, max:int)
    requires a != null;
    requires 0<= min <= max <= a.Length;
    reads a;
    {
      forall j, k :: min <= j < k < max ==> a[j] <= a[k]
    }

method FindMin(a: array<int>, from: int) returns (min: int)

    requires  a != null && a.Length >= 1
	requires  0 <= from < a.Length
	ensures from <= a.Length
	ensures  from <= min < a.Length
	ensures forall k :: from <= k < a.Length ==> a[k] >= a[min]

{
    var i := from;
    min := from;
    while i < a.Length
	   decreases a.Length - i;
       invariant from <= i <= a.Length
       invariant from <= min < a.Length
       invariant forall k :: from <= k < i ==> a[k] >= a[min]
    {
      if a[i] <= a[min] {min := i;}
      
      i := i+1;
     }
   return min;
}

 method SelectionSort ( a: array<int> ) 

    requires a != null && a.Length >=1
	modifies a
	ensures sorted(a, a.Length)

	{ 
	var min, current :=  0, 0;
	
	while (current < a.Length) 

	invariant 0 <= current <= a.Length
	invariant sorted(a,current)
	invariant forall k, l :: 0 <= k < current <= l < a.Length ==> a[k] <= a[l];
	
	{
	min := FindMin (a, current);
	assert a[min] <= a[current];
	a[min], a[current] := a[current], a[min];
	assert a[min] >= a[current];
	current := current +1;
	}
	}


	method InsertionSort ( a:array<int> ) 
		requires a != null && a.Length >= 1 
		modifies a 
		ensures sorted(a, a.Length)
	{    var i ,j, k , t:= 1,0, 0,0;	      
		  while ( i < a.Length )
		  invariant 0 <= i <= a.Length;
		  invariant sorted(a, i);
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


	