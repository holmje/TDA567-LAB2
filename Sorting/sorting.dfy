class sorting{
  
  /*
  1a. Write a predicate sorted that takes a sequence of integers (seq<int>). The predicate should be true if and only if the sequence is sorted in increasing order. 
  1b. There are often many ways to express equivalent properties, but some work better than others for program verification. Write a second predicate sorted' that is equivalent, but uses a different definition. 
  */
  
  predicate sorted(s : seq<int>)
  {
      forall i,j :: 0<= i < j < |s| ==> s[i] <= s[j]
  }
  
    predicate sorted2(s : seq<int>)
  {
   0 < |s| ==>  (forall i :: 0 < i < |s| ==> s[0] <= s[i]) && sorted2(s[1..])
  }
}
