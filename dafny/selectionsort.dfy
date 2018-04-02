predicate sorted(a:array<int>, min:int, max:int)
 requires 0<= min <= max <= a.Length
 reads a
 {
      forall j, k :: min <= j < k < max ==> a[j] <= a[k]
}

method FindMin(a: array<int>, from: int) returns (min: int)
requires a.Length >= 1
requires  0 <= from < a.Length
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
requires  a.Length >=1
modifies a
ensures sorted(a, 0, a.Length)
{ 
	   var min, current :=  0, 0;
	
	   while (current < a.Length) 
	   invariant 0 <= current <= a.Length
	   invariant sorted(a, 0, current)
	   invariant forall k, l :: 0 <= k < current <= l < a.Length ==> a[k] <= a[l];
	   {
	     min := FindMin (a, current);
	     a[min], a[current] := a[current], a[min];
	     current := current +1;
	   }
}