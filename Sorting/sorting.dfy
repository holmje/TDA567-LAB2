class sorting{
  
  
  /* 1a. Write a predicate sorted that takes a sequence of integers (seq<int>). 
  * The predicate should be true if and only if the sequence is sorted in increasing order. 
  */
  predicate sorted(s : seq<int>)
  {
      forall i,j :: 0<= i < j < |s| ==> s[i] <= s[j]
  }
  
  /* 1b. There are often many ways to express equivalent properties, but some work better than others for program verification.  
  * Write a second predicate sorted' that is equivalent, but uses a different definition. 
  */
  predicate sorted'(s : seq<int>)
  {
   0 < |s| ==>  (forall i :: 0 < i < |s| ==> s[0] <= s[i]) && sorted2(s[1..])
  }
  


  // 2a. Write one lemma that expresses the property if a sequence is sorted', then it is sorted.
  ghost method sorted2thensorted1(a : seq<int>)
  requires sorted'(a);
  ensures sorted(a);
  {
  }
  
  // 2b. Another that expresses the property if a sequence is sorted, then it is sorted'.
   ghost method sorted1thensorted2(a : seq<int>)
   requires sorted(a);
   ensures sorted'(a);
   {
   }
   	
   //3a. Explain the meaning of the predicate p below.
   predicate p(a : seq<int>, b : seq<int>)
   {
      multiset(a) == multiset(b)
   }
   
   /*
   * Multisets are like sets in almost every way, except that they keep track of how many copies of each element they have. 
   * Duplicates are ignored, Like sets, multisets are unordered. 
   * Therefor the statement above us true as long as the sets contain the same integers. The length of the sequence is irrelevant.
   * For instance; {1,2,3,3} == {1,2,3} and {1,2,3,4,5} == {2,3,4,1,5}
   * Therefor the predicate p actually checks if the set contains the same numbers and no others, duplicates are OK
   */
   
   /* 3b. Define another predicate p' that is equivalent 
   *  to p but does not use multisets. You may find it useful to define an auxiliary function.
   */ 
    predicate p'(a : seq<int>, b : seq<int>)    
    requires |a| == |b|;
    ensures p();
    {
    	forall i :: count(a,i) == count(b,i)
    }   
    
    function count(a: seq<int>, i : int): nat
 	{
    if |a| == 0 
      	then 0 
    else
    	(if a[0] == i then 1 else 0) + count(a[1..], i)
  	}
  	/*
  	 *4a. Write a full specification for a method that takes an array<int> and sorts it in place. You don't have to write the
  	 * full method, only its specification. Note: we have defined our properties on sequences (which are immutable objects) but the 
  	 * program should be defined on arrays. To convert an array t into a sequence, use the "slice" notation t[..]
	*/
	
	 method sortArray(a : array<int>)
  	 modifies a;
 	 requires a != null && sorted'(a[..]);
 	 ensures sorted'(a[..]);
 	 ensures p(a[..], old(a[..]))
     {
     }
	
	/*4b. The specification that you wrote in (4a) should use the predicate p. If it doesn't, your contract is
	 *under-specified: not all programs that satisfy it are sorting algorithms. In order to illustrate this: take
 	 *the under-specified contract (the specification in (4a) minus the part that uses the predicate p) and write a simple
  	 */program that satisfies it. (optionally, write it and verify it in Dafny). 
  
}
