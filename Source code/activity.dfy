datatype Job = Tuple(jobStart: int, jobEnd: int, profit: int)

predicate validProblem(jobs: seq<Job>)
{
  1 <= |jobs| && validJobsSeq(jobs) && sortedByActEnd(jobs) && distinctJobsSeq(jobs)
}

predicate validJob(job: Job)
{
  job.jobStart < job.jobEnd && job.profit >= 0
}

predicate validJobsSeq(jobs: seq<Job>)
{
  forall job :: job in jobs ==> validJob(job)
}

predicate  distinctJobs(j1: Job, j2: Job)
  requires validJob(j1) && validJob(j2)
{
  j1.jobStart != j2.jobStart || j1.jobEnd != j2.jobEnd
}

predicate distinctJobsSeq(s: seq<Job>)
  requires validJobsSeq(s)
{
  forall i, j :: 0 <= i < j < |s| ==> distinctJobs(s[i], s[j])
}

predicate JobComparator(job1: Job, job2: Job)
{
  job1.jobEnd <= job2.jobEnd
}

predicate sortedByActEnd(s: seq<Job>)
  requires validJobsSeq(s)
{
  forall i, j :: 0 <= i < j < |s| ==> JobComparator(s[i], s[j])
}

predicate overlappingJobs(j1:Job, j2:Job)
  requires validJob(j1)
  requires validJob(j2)
{
  j1.jobEnd > j2.jobStart &&  j2.jobEnd > j1.jobStart
}

predicate hasNoOverlappingJobs(partialSol: seq<int>, jobs: seq<Job>)
  requires validJobsSeq(jobs)
{
  |partialSol| <= |jobs|  && forall i, j :: 0 <= i < j < |partialSol| ==> (partialSol[i] == 1 && partialSol[j] == 1) ==> !overlappingJobs(jobs[i], jobs[j])
}


function PartialSolProfit(solution: seq<int>, jobs: seq<Job>, index: int): int
  requires 0 <= index <= |solution| <= |jobs|
  decreases |solution| - index
  ensures PartialSolProfit(solution, jobs, index) == if index == |solution| then 0 else solution[index] * jobs[index].profit + PartialSolProfit(solution, jobs, index + 1)
{

  if index == |solution| then 0 else solution[index] * jobs[index].profit + PartialSolProfit(solution, jobs, index + 1)
}

// prob + sub
predicate isPartialSol(partialSol: seq<int>, jobs: seq<Job>, length: int)
  requires validJobsSeq(jobs)
  requires 0 <= length <= |jobs| 
{
  |partialSol| == length &&
  forall i :: 0 <= i <= |partialSol| - 1 ==> (0 <= partialSol[i] <= 1) && hasNoOverlappingJobs(partialSol, jobs)
}


ghost predicate isOptParSol(partialSol: seq<int>, jobs: seq<Job>, length: int)
  requires validJobsSeq(jobs)
  requires 1 <= |jobs|
  requires length == |partialSol|
  requires 1 <= |partialSol| <= |jobs|
{
  isPartialSol(partialSol, jobs, length) &&
  forall otherSol :: isPartialSol(otherSol, jobs, length) ==> HasLessProf(otherSol, jobs, PartialSolProfit(partialSol, jobs, 0), 0)
}

predicate HasProfit(partialSol: seq<int>, jobs: seq <Job>, position : int , profit: int )
  requires validJobsSeq(jobs)
  requires |jobs| >= 1
  requires |partialSol| <= |jobs|
  requires 0 <= position < |partialSol|
{
  PartialSolProfit(partialSol, jobs, position) ==  profit
}

ghost predicate isOptParSolDP(partialSol: seq<int>, jobs: seq<Job>, length : int, profit:int)
  requires validJobsSeq(jobs)
  requires 1 <= |partialSol|
  requires 1 <= length <= |jobs|
{
  |partialSol| == length && isOptParSol(partialSol, jobs, length) && HasProfit(partialSol, jobs, 0,  profit)
}

ghost predicate OptParSolutions(allSol: seq<seq<int>>, jobs: seq<Job>, dp:seq<int>, index: int)
  requires validJobsSeq(jobs)
  requires |dp| == |allSol| == index
  requires 1 <= index <= |jobs|
{
  forall i : int :: 0 <= i < index ==> |allSol[i]| == i + 1  && isOptParSolDP(allSol[i], jobs, i + 1, dp[i])
}

predicate isSolution(solution: seq<int>, jobs: seq <Job>)
  requires validJobsSeq(jobs)
{
  isPartialSol(solution, jobs, |jobs|)
}


ghost predicate isOptimalSolution(solution: seq<int>, jobs: seq<Job>)
  requires validJobsSeq(jobs)
  requires 1 <= |jobs|
  requires |solution| == |jobs|
{
  isSolution(solution, jobs) &&
  forall otherSol :: isSolution(otherSol, jobs) ==> PartialSolProfit(solution, jobs, 0) >=  PartialSolProfit(otherSol, jobs, 0)
    //HasLessProf(otherSol, jobs, PartialSolProfit(solution, jobs, 0), 0)
}

predicate containsOnlyZeros(partialSol: seq<int>)
{
  forall x :: 0 <= x < |partialSol| ==> partialSol[x] == 0
}

predicate partialSolutionWithJobI(partialSol: seq<int>, jobs: seq<Job>,  i: int)
  requires validJobsSeq(jobs)
  requires 0 <= i < |partialSol| <= |jobs|
{
  isPartialSol(partialSol, jobs, |partialSol|) && partialSol[i] == 1
}

predicate partialSolutionWithoutJobI(partialSol: seq<int>, jobs: seq<Job>,  i: int)
  requires validJobsSeq(jobs)
  requires 0 <= i < |partialSol| <= |jobs|
{
  isPartialSol(partialSol, jobs, |partialSol|) && partialSol[i] == 0
}

predicate HasLessProf(partialSol: seq<int>, jobs: seq<Job>,  maxProfit: int, position: int)
  requires validJobsSeq(jobs)
  requires 0 <= position < |partialSol| <= |jobs|
{
  PartialSolProfit(partialSol, jobs, position) <= maxProfit
}

predicate HasMoreProfit(partialSol: seq<int>, jobs: seq<Job>,  maxProfit: int, position: int)
  requires validJobsSeq(jobs)
  requires 0 <= position < |partialSol| <= |jobs|
{
  PartialSolProfit(partialSol, jobs, position) > maxProfit
}


function ProfitParSolStartFinishPos(solution: seq<int>, jobs: seq<Job>, startPos: int, endPos: int): int
  requires 0 <= startPos <= endPos <= |solution| <= |jobs|
  decreases |solution| - startPos
  ensures ProfitParSolStartFinishPos(solution, jobs, startPos, endPos) == if startPos == endPos then 0 else solution[startPos] * jobs[startPos].profit + ProfitParSolStartFinishPos(solution, jobs, startPos + 1, endPos)
{

  if startPos == endPos then 0 else solution[startPos] * jobs[startPos].profit + ProfitParSolStartFinishPos(solution, jobs, startPos + 1, endPos)
}


lemma AssociativityOfProfitFunc(partialSolPrefix : seq<int>, jobs: seq<Job>, val: int, index: int)
  requires 1 <= |jobs|
  requires validJobsSeq(jobs)
  requires 0 <= index <= |partialSolPrefix|
  requires 0 <= val <= 1
  requires 0 <= |partialSolPrefix| < |jobs| //pentru a ne asiguram ca nu depasim nr de job-uri
  decreases |partialSolPrefix| - index
  ensures PartialSolProfit(partialSolPrefix, jobs, index) + val * jobs[|partialSolPrefix|].profit ==
          PartialSolProfit(partialSolPrefix + [val], jobs, index)
{
  //inductie prin recursivitate
  if |partialSolPrefix| == index { //pentru ultima valoare se demonstreaza

  }
  else
  {
    AssociativityOfProfitFunc(partialSolPrefix , jobs, val, index + 1);
  }
}

lemma EqOfProfitFuncFromIndToEnd(partialSolution: seq<int>, jobs: seq<Job>, startPos: int)
  requires 0 <= startPos <= |partialSolution|  <= |jobs|
  ensures ProfitParSolStartFinishPos(partialSolution, jobs, startPos, |partialSolution|) == PartialSolProfit(partialSolution, jobs, startPos)
  decreases |partialSolution| - startPos
{

  if startPos == |partialSolution|
  {

  }
  else
  {
    EqOfProfitFuncFromIndToEnd(partialSolution, jobs, startPos + 1);
  }
}


lemma EqOfProfFuncUntilIndex(partialSolution: seq<int>, jobs: seq<Job>, startPos: int, index: int) //PartialSolProfit(partialSol[..j+1], jobs, 0)
  requires 0 <= startPos <= index <= |partialSolution| <= |jobs|
  ensures  ProfitParSolStartFinishPos(partialSolution, jobs, startPos, index) == PartialSolProfit(partialSolution[..index], jobs, startPos)
  decreases index - startPos
{
  if startPos == index{
    assert ProfitParSolStartFinishPos(partialSolution, jobs, startPos, index) == 0;
  }
  else{
    EqOfProfFuncUntilIndex(partialSolution, jobs, startPos + 1, index);
  }
}


lemma SplitSequenceProfitEquality(partialSol: seq<int>, jobs: seq<Job>, startPos: int, index: int)
  requires 0 <= index < |partialSol|
  requires 0 <= startPos < index
  requires 0 <= |partialSol| <= |jobs|
  ensures ProfitParSolStartFinishPos(partialSol, jobs, startPos, |partialSol|)
   == ProfitParSolStartFinishPos(partialSol, jobs, startPos, index) 
   + ProfitParSolStartFinishPos(partialSol, jobs, index, |partialSol|)
  decreases  index - startPos
{

}

lemma ProfitLastElem(partialSol: seq<int>, jobs: seq<Job>, i: int)
  requires validJobsSeq(jobs)
  requires 0 < i < |partialSol| <= |jobs|
  requires |partialSol| == i + 1
  requires partialSolutionWithJobI(partialSol, jobs, i)
  ensures PartialSolProfit(partialSol, jobs, i) == jobs[i].profit
{
}


lemma ComputeProfitWhenOnly0BetweenJI(partialSol: seq<int>, jobs: seq<Job>, i: int, j: int)
  requires validJobsSeq(jobs)
  requires 0 <= j < i < |partialSol| <= |jobs|
  requires |partialSol| == i + 1
  requires isPartialSol(partialSol, jobs, |partialSol|)
  requires partialSolutionWithJobI(partialSol, jobs, i)
  requires PartialSolProfit(partialSol, jobs, i) == jobs[i].profit
  requires forall k :: j < k < i ==> partialSol[k] == 0
  ensures PartialSolProfit(partialSol, jobs, j + 1) == jobs[i].profit
  decreases i - j
{
  if j == i - 1
  {
    assert PartialSolProfit(partialSol, jobs, j + 1) == jobs[i].profit;
  }
  else
  {
    ComputeProfitWhenOnly0BetweenJI(partialSol, jobs, i, j + 1);
  }

}

lemma HasMoreProfThanOptParSol(optimalPartialSol: seq<int>, jobs: seq<Job>, partialSol: seq<int>)
  requires validJobsSeq(jobs)
  requires 1 <= |optimalPartialSol| <= |jobs|
  requires |optimalPartialSol| == |partialSol|
  requires isPartialSol(partialSol, jobs, |partialSol|)
  requires isOptParSol(optimalPartialSol, jobs, |optimalPartialSol|)
  requires PartialSolProfit(partialSol, jobs, 0) > PartialSolProfit(optimalPartialSol, jobs, 0)
  ensures !isOptParSol(optimalPartialSol, jobs, |optimalPartialSol|)
{
  var other_profit := PartialSolProfit(partialSol, jobs, 0);
  var optParSolProfit := PartialSolProfit(optimalPartialSol, jobs, 0);
  assert forall otherSol:: isPartialSol(otherSol, jobs, |optimalPartialSol|) ==> HasLessProf(otherSol, jobs, optParSolProfit, 0);
  assert other_profit > optParSolProfit;
  assert !isOptParSol(optimalPartialSol, jobs, |optimalPartialSol|);

}

lemma OtherSolHasLessProfThenMaxProfit2(partialSol: seq<int>, jobs : seq<Job>, i: int, j : int, max_profit : int, allSol : seq<seq<int>>, dp: seq<int>)
  requires validJobsSeq(jobs)
  requires 1 <= |jobs|
  requires 0 <= j < i < |jobs|
  requires |allSol| == |dp| == i  
  requires OptParSolutions(allSol, jobs, dp, i)
  requires isOptParSol(allSol[j], jobs, j + 1) 
  requires max_profit == dp[j] + jobs[i].profit 
  requires forall k :: j < k < i ==> overlappingJobs(jobs[k], jobs[i])
  requires !overlappingJobs(jobs[j], jobs[i])
  requires |partialSol| == i + 1
  requires partialSolutionWithJobI(partialSol, jobs, i)
  requires PartialSolProfit(partialSol, jobs, i) == jobs[i].profit;
  requires isPartialSol(partialSol, jobs, i + 1)
  requires forall k :: j < k < i ==> partialSol[k] == 0
  ensures HasLessProf(partialSol, jobs, max_profit, 0)
{

  var k : int := i - 1; // pe pozitia i se afla job-ul i
  assert |partialSol| == i + 1;
  assert j <= k < i;
  //assert !exists k' :: k < k' < i;

  assert forall k' :: k < k' < i ==> partialSol[k'] == 0; //asta vreau sa demonstrez ==> ca am doar 0 -rouri pe pozitiile i - 1 ...0
  assert PartialSolProfit(partialSol, jobs, i) == jobs[i].profit;

  ComputeProfitWhenOnly0BetweenJI(partialSol, jobs, i, j);
  assert PartialSolProfit(partialSol, jobs, j + 1) == jobs[i].profit;

  //presupunem contrariul
  if !HasLessProf(partialSol, jobs, max_profit, 0) //presupunem ca ar exista o solutie partiala care indeplineste conditiile si care
    //sa aiba profitul mai mare decat max_profit
  {
    var profit' := PartialSolProfit(partialSol, jobs, 0);
    assert max_profit == dp[j] + jobs[i].profit;

    assert HasMoreProfit(partialSol, jobs, max_profit, 0);
    assert !HasLessProf(partialSol, jobs, max_profit, 0);

    assert partialSol[..j+1] + partialSol[j+1..] == partialSol;
    //apelam lemmele ajutatoare pt a demonstra linia 400
    SplitSequenceProfitEquality(partialSol, jobs, 0, j + 1);
    EqOfProfitFuncFromIndToEnd(partialSol, jobs, 0);
    EqOfProfFuncUntilIndex(partialSol, jobs, 0, j + 1);
    EqOfProfitFuncFromIndToEnd(partialSol, jobs, j + 1);

    assert PartialSolProfit(partialSol[..j + 1], jobs, 0) + PartialSolProfit(partialSol, jobs, j + 1) == PartialSolProfit(partialSol, jobs, 0);
    assert PartialSolProfit(partialSol, jobs, j + 1) == jobs[i].profit; //(2)

    var partialSol' :seq<int> := partialSol[..j + 1];
    assert isPartialSol(partialSol', jobs, j + 1);
    var profit := PartialSolProfit(partialSol', jobs, 0); //(1)

    assert |partialSol'| == j + 1;
    assert profit + jobs[i].profit == profit';
    assert profit + jobs[i].profit > max_profit; //ipoteza de la care am plecat
    assert profit > max_profit - jobs[i].profit;
    assert profit > dp[j];
    HasMoreProfThanOptParSol(allSol[j], jobs, partialSol');
    assert !isOptParSol(allSol[j], jobs, j + 1); //contradictie
    //assume false;
    assert false;
  }
  assert HasLessProf(partialSol, jobs, max_profit, 0);
}

//demonstram ca daca toate job-urile dintre i si j se suprapun este imposibil sa avem 1 (=> suprapunere=> !solutie partiala)
lemma OnlY0WhenOverlapJobs(partialSol: seq<int>, jobs: seq<Job>, i: int, j: int)
  requires validJobsSeq(jobs)
  requires 0 <= j < i < |partialSol|  <= |jobs|
  requires isPartialSol(partialSol, jobs, i + 1)
  requires partialSolutionWithJobI(partialSol, jobs, i)
  requires forall k :: j < k < i ==> overlappingJobs(jobs[k], jobs[i])
  requires hasNoOverlappingJobs(partialSol, jobs);
  requires !overlappingJobs(jobs[j], jobs[i])
  ensures forall k :: j < k < i ==> partialSol[k] == 0
{
  assert isPartialSol(partialSol, jobs, i + 1);
  assert hasNoOverlappingJobs(partialSol, jobs);
  assert forall k :: j < k < i ==> overlappingJobs(jobs[k], jobs[i]);
  forall k | j < k < i < |partialSol|
    ensures partialSol[k] == 0
  {
    if partialSol[k] == 1
    {
      assert overlappingJobs(jobs[k], jobs[i]);
      //assert !hasNoOverlappingJobs(partialSol, jobs);
      assert !isPartialSol(partialSol, jobs, i + 1);
      assert false;
    }

  }
}

method  OptParSolWhenNonOverlapJob(jobs: seq <Job>, i: int, dp: seq<int>, allSol :seq<seq<int>>, j : int) returns (maxProfit:int, partialSolution: seq<int>, length: int)
  requires validProblem(jobs)
  requires 0 <= j < i < |jobs|
  requires |allSol| == i
  requires |dp| == i
  requires OptParSolutions(allSol, jobs, dp, i)
  requires !overlappingJobs(jobs[j], jobs[i]);
  requires jobs[j].jobEnd <= jobs[i].jobStart
  requires forall k :: j < k < i ==> overlappingJobs(jobs[k], jobs[i]) //job-urile de pe pozitiile j+1..i-1 se suprapun cu i
  requires !overlappingJobs(jobs[j], jobs[i]);
  ensures isPartialSol(partialSolution, jobs, i + 1)
  ensures partialSolutionWithJobI(partialSolution, jobs, i)
  ensures maxProfit == PartialSolProfit(partialSolution, jobs, 0)
  ensures forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, maxProfit, 0)
  ensures length == i + 1;
{
  var partialSolutionPrefix : seq<int> := [];
  var max_profit : int := 0 ;
  length := 0;

  partialSolutionPrefix := allSol[j];
  length := length + |allSol[j]|;

  assert forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolutionPrefix[i] <= 1; //toate elementele sunt 0 sau 1
  assert hasNoOverlappingJobs(partialSolutionPrefix, jobs); //nu are job-uri care se suprapun pentru ca allSol[j] este solutie partiala optima

  max_profit := max_profit + dp[j]; //adaug profitul pt solutia partiala optima (cu job-uri pana la pozitia j)

  var nr_of_zeros := i - |allSol[j]|; // nr de elemente dintre i si j

  while nr_of_zeros > 0
    decreases nr_of_zeros
    invariant 0 <= nr_of_zeros <= i - |allSol[j]| //setam limitele pentru nr_of_zeros
    decreases i - length
    invariant |allSol[j]| <= length <= i //imp
    invariant |partialSolutionPrefix| == length
    invariant forall k :: 0 <= k <= length - 1 ==> 0 <= partialSolutionPrefix[k] <= 1
    invariant length < |jobs|;
    invariant length == i - nr_of_zeros
    invariant hasNoOverlappingJobs(partialSolutionPrefix, jobs)
    invariant forall k :: j < k < |partialSolutionPrefix| ==> partialSolutionPrefix[k] == 0
    invariant max_profit == PartialSolProfit(partialSolutionPrefix, jobs, 0)
  {
    //assume false;
    AssociativityOfProfitFunc(partialSolutionPrefix, jobs, 0, 0); //demonstram ca daca adaugam 0 profitul "ramane acelasi" 0 * jobs[..]
    assert max_profit == PartialSolProfit(partialSolutionPrefix, jobs, 0);
    partialSolutionPrefix :=  partialSolutionPrefix + [0]; //se adauga de nr_of_zeros ori
    assert length + nr_of_zeros < |jobs|;
    length := length + 1;
    nr_of_zeros := nr_of_zeros - 1;
    assert max_profit == PartialSolProfit(partialSolutionPrefix, jobs, 0);
  }

  assert length == i;
  assert |partialSolutionPrefix| == i ;

  assert forall k :: j < k < i ==> partialSolutionPrefix[k] == 0;
  assert forall k :: j < k < i ==> overlappingJobs(jobs[k], jobs[i]); //stim ca toate job-urile strict mai mari decat j se suprapun cu i

  assert isPartialSol(partialSolutionPrefix, jobs, i);

  assert hasNoOverlappingJobs(partialSolutionPrefix + [1], jobs); // lemmas before

  AssociativityOfProfitFunc(partialSolutionPrefix, jobs, 1, 0); //apelam inainte sa adaugam 1
  partialSolutionPrefix := partialSolutionPrefix + [1]; //includem si job-ul i (solutia partiala ce contine job-ul i)
  length := length + 1;
  max_profit := max_profit + jobs[i].profit;

  assert isPartialSol(partialSolutionPrefix, jobs, i + 1);
  assert max_profit == PartialSolProfit(partialSolutionPrefix, jobs, 0); //lemma
  forall partialSol | |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i)
    ensures HasLessProf(partialSol, jobs, max_profit, 0)
  {
    //assume forall k :: j < k < i ==> partialSol[k] == 0;
    OnlY0WhenOverlapJobs(partialSol, jobs, i, j); //stim ca daca toate job-urile dintre i si j se suprapun, inseamna ca putem avea doar 0-uri
    assert forall k :: j < k < i ==> partialSol[k] == 0;
    ProfitLastElem(partialSol, jobs, i);
    assert PartialSolProfit(partialSol, jobs, i) == jobs[i].profit;
    OtherSolHasLessProfThenMaxProfit2(partialSol, jobs, i, j, max_profit, allSol, dp);
    //assume false;
  }

  //assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, max_profit, 0) ;
  maxProfit := max_profit;
  partialSolution := partialSolutionPrefix;
}

//lemma ajutor pt functia de mai jos
//demonstram ca daca toate job-urile din fata lui i se suprapun cu acesta nu putem avea decat 0 => 1 imposibil (!solutie partiala)
//=> profitul maxim pentru o astfel de solutie partiala este maxim jobs[i].profit
lemma OtherSolHasLessProfThenMaxProfit(jobs : seq<Job>, i: int, max_profit : int)
  requires validJobsSeq(jobs)
  requires 0 < i < |jobs|
  requires max_profit == jobs[i].profit
  requires forall j :: 0 <= j < i ==> overlappingJobs(jobs[j], jobs[i])
  ensures forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, max_profit, 0)
{
  forall partialSol | |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i)
    ensures HasLessProf(partialSol, jobs, max_profit, 0) { // <=
    assert isPartialSol(partialSol, jobs, i + 1);
    var k := i - 1; // pe pozitia i se afla job-ul i
    assert |partialSol| == i + 1;
    assert -1 <= k < i;
    //assert !exists k' :: k < k' < i;
    assert forall k' :: k < k' < i ==> partialSol[k'] == 0; //asta vreau sa demonstrez ==> ca am doar 0 -rouri pe pozitiile i - 1 ...0
    assert PartialSolProfit(partialSol, jobs, k + 1) == jobs[i].profit;

    while k >= 0 //k > 0 , ajungeam pana la 1 si invariantul era ori k' >= k (imposibil), ori k' > k => ultimele pozitii verificare erau > 1 = 2 (1)
      decreases k
      invariant -1 <= k < i
      invariant forall k' :: k < k' < i ==> partialSol[k'] == 0 //asta vreau sa demonstrez ==> ca am doar 0 -rouri pe pozitiile i - 1 ...0
      invariant PartialSolProfit(partialSol, jobs, k + 1) == jobs[i].profit //demonstram de la 0 la i pentru toate job-urile
    {
      // assume false;
      if partialSol[k] == 1 {

        //assume false;
        assert partialSol[i] == 1;
        assert overlappingJobs(jobs[k], jobs[i]);
        assert !isPartialSol(partialSol, jobs, i + 1); //demonstram ca daca ar fi 1 s-ar contrazice cu ipoteza ==> doar 0-uri
        // assume false;
        assert false;

      }
      assert forall k' :: k < k' < i ==> partialSol[k'] == 0;
      assert partialSol[k] == 0;
      assert forall k' :: k <= k' < i ==> partialSol[k'] == 0; //in while demonstrezi pentru k' = k
      k := k - 1;
      assert forall k' :: k < k' < i ==> partialSol[k'] == 0;
      // assume false;
    }
    //assume false;
    assert PartialSolProfit(partialSol, jobs, 0) == jobs[i].profit; //lemma tot 0, profit 0
  }
}

//DEMONSTRATA doar 0-uri in fata lui i
//demonstram ca solutia de lungime i+1 ce contine job-ul i care se obtine cu aceste preconditii este partiala + optima
method  OptParSolWhenOverlapJob(jobs: seq <Job>, i: int, dp: seq<int>) returns (maxProfit:int, partialSolution: seq<int>, length: int)
  requires validProblem(jobs)
  requires 1 <= i < |jobs|
  requires |dp| == i
  requires forall k :: -1 < k < i ==> overlappingJobs(jobs[k], jobs[i]) //toate job-urile se suprapun cu i
  ensures isPartialSol(partialSolution, jobs, i + 1)
  ensures maxProfit == PartialSolProfit(partialSolution, jobs, 0)
  ensures forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, maxProfit, 0)
  ensures length == i + 1;
  ensures partialSolutionWithJobI(partialSolution, jobs, i)
{
  // assume false;
  var partialSolutionPrefix : seq<int> := [];
  var max_profit : int := 0 ;
  length := 0;

  assert forall k :: -1 < k < i ==> overlappingJobs(jobs[k], jobs[i]);

  var nr_of_zeros := i;

  while nr_of_zeros > 0
    decreases nr_of_zeros
    decreases i - length
    invariant 0 <= nr_of_zeros <= i
    invariant |partialSolutionPrefix| == length
    invariant forall i :: 0 <= i <= length - 1 ==> 0 <= partialSolutionPrefix[i] <= 1;
    invariant length == i - nr_of_zeros
    invariant 0 <= length <= i
    invariant hasNoOverlappingJobs(partialSolutionPrefix, jobs)
    invariant max_profit == PartialSolProfit(partialSolutionPrefix, jobs, 0)
    invariant max_profit == 0
    invariant forall k :: 0 <= k < |partialSolutionPrefix| ==> partialSolutionPrefix[k] == 0
    //invariant isPartialSol(partialSolutionPrefix, jobs, length)
  {
    AssociativityOfProfitFunc(partialSolutionPrefix, jobs, 0, 0);
    partialSolutionPrefix :=  partialSolutionPrefix + [0];
    length := length + 1;
    nr_of_zeros := nr_of_zeros - 1;
    max_profit := max_profit + 0 ;
  }
  assert length == i;
  assert containsOnlyZeros(partialSolutionPrefix);
  assert partialSolutionWithJobI(partialSolutionPrefix + [1], jobs, i);

  assert forall k :: 0 <= k < i ==> partialSolutionPrefix[k] == 0;
  assert forall k :: 0 <= k < i ==> overlappingJobs(jobs[k], jobs[i]); //preconditie

  assert isPartialSol(partialSolutionPrefix, jobs, i);

  AssociativityOfProfitFunc(partialSolutionPrefix, jobs, 1, 0); //apelata pentru max_profit inainte de a adauga 1

  partialSolutionPrefix := partialSolutionPrefix + [1]; //includem si job-ul i (solutia partiala ce contine job-ul i)
  max_profit := max_profit + jobs[i].profit; //contine doar job-ul i
  length := length + 1;

  OtherSolHasLessProfThenMaxProfit(jobs, i, max_profit); //demonstram optimalitatea
  assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, max_profit, 0) ;

  //assert |partialSolutionPrefix| == i + 1;
  assert max_profit == PartialSolProfit(partialSolutionPrefix, jobs, 0);
  assert isPartialSol(partialSolutionPrefix, jobs, length);

  partialSolution := partialSolutionPrefix;
  maxProfit := max_profit;
}

//functia MaxProfitWithJobI intoarce solutia partiala si optima cu job-ul i inclus
method MaxProfitWithJobI(jobs: seq <Job>, i: int, dp: seq<int>, allSol :seq<seq<int>>) returns (maxProfit:int, optParSolWithI: seq<int>)
  requires validProblem(jobs)
  requires 1 <= i < |jobs|
  requires |allSol| == i
  requires |dp| == i
  requires OptParSolutions(allSol, jobs, dp, i)
  ensures isPartialSol(optParSolWithI, jobs, i + 1)
  ensures maxProfit == PartialSolProfit(optParSolWithI, jobs, 0)
  ensures partialSolutionWithJobI(optParSolWithI, jobs, i)
  ensures forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, maxProfit, 0)
{

  var max_profit := 0;
  var partialSolutionPrefix : seq<int> := [];
  var partialSolution : seq<int> := [];
  var j := i - 1;
  var length := 0;

  //cautam un job care nu se suprapune cu i si demonstram ca toate job-urile dintre j si i se suprapun cu i
  while j >= 0 && jobs[j].jobEnd > jobs[i].jobStart //
    invariant - 1 <= j < i
    invariant forall k :: j < k < i ==> jobs[k].jobEnd > jobs[i].jobStart //se suprapun
    invariant forall k :: j < k < i ==> validJob(jobs[k])
    invariant forall k :: j < k < i ==> JobComparator(jobs[k], jobs[i]) //din OrderedByEnd
    invariant forall k :: j < k < i ==> jobs[k].jobEnd > jobs[k].jobStart //din ValidJob
    invariant forall k :: j < k < i ==> overlappingJobs(jobs[k], jobs[i]) //stiu doar despre primul job j(ultima val a while-ului) nu se suprapune cu i
  {
    j := j - 1;
  }

  assert  j != -1 ==> !overlappingJobs(jobs[j], jobs[i]);

  //assume false;
  if j >= 0 //inseamna ca a gasit un job j cu care nu se suprapune cu i (pe o pozitie >= 0)
  {

    max_profit, partialSolution, length := OptParSolWhenNonOverlapJob(jobs, i, dp, allSol, j);
    //assume false;

  }
  else //nu am gasit niciun job j care sa nu se suprapuna cu i
  {
    //assume false;
    max_profit, partialSolution, length := OptParSolWhenOverlapJob(jobs, i, dp);

  }
  assert forall k :: 0 <= k < length ==> 0 <= partialSolution[k] <= 1; 
  assert hasNoOverlappingJobs(partialSolution, jobs);
  assert |partialSolution| == length;
  assert isPartialSol(partialSolution, jobs, length);
  assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, max_profit, 0) ;
  maxProfit := max_profit;
  optParSolWithI := partialSolution;
  assert maxProfit == PartialSolProfit(partialSolution, jobs, 0);
}

//demonstram ca daca adaugam [0] la o secventa profitul acesteia ramane acelasi ca inainte de adaugare
lemma NotAddingAJobKeepsSameProfit(partialSol: seq<int>, jobs: seq <Job>, index: int)
  requires validJobsSeq(jobs)
  requires 0 <= index <= |partialSol| < |jobs|
  decreases |partialSol| - index
  ensures PartialSolProfit(partialSol, jobs, index) == PartialSolProfit(partialSol + [0], jobs, index)
{
  if |partialSol| == index {
    assert PartialSolProfit(partialSol, jobs, index) == PartialSolProfit(partialSol + [0], jobs, index);

  }
  else
  {
    NotAddingAJobKeepsSameProfit(partialSol, jobs, index + 1);
  }

}


//o subsecventa a unei solutii partiale este tot solutie partiala
lemma SubSeqOfPartialIsAlsoPartial(partialSol: seq<int>, jobs: seq<Job>, length: int)
  requires length + 1 == |partialSol|
  requires 0 <= length < |jobs|
  requires validJobsSeq(jobs)
  requires isPartialSol(partialSol, jobs, length + 1)
  ensures isPartialSol(partialSol[..length], jobs, length)
{

}

//lemma ajutatoare pentru metoda leadsToOptWithJobI
//demonstram ca in cazul in care profitul solutiei partiale ce contine job-ul i este mai mare decat dp[i-1] (profitul optim anterior)
//aceasta este optima
lemma optimalPartialSolutionWithJobI(i: int, jobs: seq<Job>, maxProfit: int, dp: seq<int>)
  requires validJobsSeq(jobs)
  requires 1 <= |jobs|
  requires |dp| == i
  requires 1 <= i < |jobs|
  requires dp[i - 1] < maxProfit
  requires forall partialSol :: |partialSol| == i  && isPartialSol(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, dp[i - 1], 0); //dp[i-1] profitul optim pentru job-urile de lungime i //stim din invariant
  requires forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, maxProfit, 0)
  ensures forall partialSol :: |partialSol| == i + 1 && isPartialSol(partialSol, jobs, |partialSol|) ==> HasLessProf(partialSol, jobs, maxProfit, 0);
{
  forall partialSol | |partialSol| == i + 1 && isPartialSol(partialSol, jobs, |partialSol|)
    ensures HasLessProf(partialSol, jobs, maxProfit, 0);
  {
    if partialSol[i] == 1
    {
      assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, maxProfit, 0);
      //assume false;
      //demonstrat din functia MaxProfitWithJobI
    }
    else{
      //daca nu adaug un job profitul ramane <= dp[i-1] (invariant sulutie partiala optima), care in aceasta ramura a if-ului este <= max_profit
      // ==> tranzitivitate ==> profitul curent <= dp[i] (= max_profit)
      //nu se demonstreaza
      //daca nu punem job-ul i => punem 0 si profitul este <= dp[i-1] (optim) (pasul anterior), dp[i - 1] < max_profit => tranzitivitate <= max_profit
      NotAddingAJobKeepsSameProfit(partialSol[..i], jobs, 0);
      assert partialSol == partialSol[..i] + [0];
      assert PartialSolProfit(partialSol, jobs, 0) == PartialSolProfit(partialSol[..i], jobs, 0);
      SubSeqOfPartialIsAlsoPartial(partialSol, jobs, i);
      assert isPartialSol(partialSol[..i], jobs, |partialSol[..i]|);
      assert PartialSolProfit(partialSol[..i], jobs, 0) <= dp[i - 1]; //din requires(1)
      assert PartialSolProfit(partialSol, jobs, 0)  <= dp[i - 1];
      assert dp[i - 1] < maxProfit; //care stim din preconditii ca este < maxProfit
      //assume false;
      //assume false;
      assert HasLessProf(partialSol, jobs, maxProfit, 0);

    }

  }
}

//ramura din metoda principala in care prin alegerea job-ului i se obtine un profit mai bun decat fara acesta
//metoda in care calculam solutia partiala de lungime i = solutia partiala cu job-ul i si demonstram ca aceasta este optima, stiind ca profitul acesteia este > decat dp[i-1]
method leadsToOptWithJobI(jobs: seq<Job>, dp:seq<int>, allSol: seq<seq<int>>, i: int, maxProfit: int, optParSolWithJobI: seq<int>) returns (optimalPartialSolution: seq<int>, profits:seq<int>)
  requires validProblem(jobs)
  requires 1 <= i < |jobs|
  requires |dp| == |allSol| == i
  requires isPartialSol(optParSolWithJobI, jobs, i + 1)
  requires partialSolutionWithJobI(optParSolWithJobI, jobs, i)
  requires maxProfit == PartialSolProfit(optParSolWithJobI, jobs, 0);
  requires forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, maxProfit, 0)
  requires forall partialSol :: |partialSol| == i  && isPartialSol(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, dp[i - 1], 0); //dp[i-1] profitul optim pentru job-urile de lungime i //stim din invariant
  requires dp[i - 1] < maxProfit
  ensures isPartialSol(optimalPartialSolution, jobs, i + 1)
  ensures |profits| == i + 1
  ensures profits == dp + [maxProfit]
  ensures isOptParSol(optimalPartialSolution, jobs, i + 1)
  ensures HasProfit(optimalPartialSolution, jobs, 0, profits[i])
  ensures forall partialSol :: |partialSol| == i + 1  && isPartialSol(partialSol, jobs, i + 1) ==> HasLessProf(partialSol, jobs, profits[i], 0);
{

  profits := dp + [maxProfit]; //profitul general creste deorece cu job-ul curent se obtine un profit mai mare
  assert optParSolWithJobI[i] == 1;

  optimalPartialSolution := optParSolWithJobI; //solutia contine job-ul i
  assert isPartialSol(optimalPartialSolution, jobs, i + 1);
  assert PartialSolProfit(optimalPartialSolution, jobs, 0) == maxProfit;
  assert partialSolutionWithJobI(optimalPartialSolution, jobs, i);

  //demonstram ca aceasta solutie partiala este si optima
  optimalPartialSolutionWithJobI(i, jobs, maxProfit, dp);

  assert forall partialSol :: |partialSol| == i + 1   && isPartialSol(partialSol, jobs, i + 1) ==> HasLessProf(partialSol, jobs, profits[i], 0);
  assert isOptParSol(optimalPartialSolution, jobs, i + 1);
}


lemma optimalPartialSolutionWithoutJobI(i: int, jobs: seq<Job>, maxProfit: int, dp: seq<int>, profits: seq<int>)
  requires validJobsSeq(jobs)
  requires 1 <= |jobs|
  requires 1 <= i < |jobs|
  requires |dp| == i
  requires |profits| == i + 1
  requires profits[i] == dp[i - 1]
  requires dp[i - 1] >= maxProfit
  requires forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, maxProfit, 0)
  requires forall partialSol :: |partialSol| == i  && isPartialSol(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, dp[i - 1], 0); //dp[i-1] profitul optim pentru job-urile de lungime i
  ensures forall partialSol :: |partialSol| == i + 1 && isPartialSol(partialSol, jobs, |partialSol|) ==> HasLessProf(partialSol, jobs, profits[i], 0)
{
  forall partialSol | |partialSol| == i + 1 && isPartialSol(partialSol, jobs, |partialSol|)
    ensures HasLessProf(partialSol, jobs, profits[i], 0) //profits[i] == dp[i - 1] => imi doresc sa arat ca se obtin profituri <= dp[i-1] si am reusit YEEEE:))
  {
    if partialSol[i] == 1
    {
      //stim ca toate au profitul <= max_profit, iar max_profit <= dp[i-1]
      assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, maxProfit, 0);
      assert maxProfit <= dp[i - 1];
      assert profits[i] == dp[i - 1];
      assert maxProfit <= profits[i];
      assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, profits[i], 0);
      //assume false;
    }
    else
    {
      //assume false;
      assert partialSol[i] == 0;
      //daca adugam 0 profitul ramane acelasi cu profitul de inainte de a adauga job-ul <= dp[i-1] (pasul anterior) <= dp[i - 1] SMART
      //profitul ramane dp[i-1] care stim ca este optim pentru toate solutiile partiale de lungime i - 1 din invariant
      assert partialSol[..i] + [0] == partialSol;
      NotAddingAJobKeepsSameProfit(partialSol[..i], jobs, 0);
      assert PartialSolProfit(partialSol[..i], jobs, 0) == PartialSolProfit(partialSol, jobs, 0); //<= dp[i-1] IMPORTANT
      assert isPartialSol(partialSol[..i], jobs, |partialSol[..i]|);
      assert forall partialSol :: |partialSol| == i  && isPartialSol(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, dp[i - 1], 0);
      assert PartialSolProfit(partialSol[..i], jobs, 0) <= dp [i - 1]; //dp[i-1] profit optim ..i !!IMPORTANT
      assert PartialSolProfit(partialSol, jobs, 0) <= dp[i - 1];
      assert profits[i] == dp[i - 1];
      assert PartialSolProfit(partialSol, jobs, 0) <= profits[i];
    }
  }
}

//ramura in care prin alegerea job-ului i se obtine un profit <= cu cel anterior (dp[i-1]) si nu se adauga job-ul i la solutia optima
method leadsToOptWithoutJobI(jobs: seq<Job>, dp:seq<int>, allSol: seq<seq<int>>, i: int, maxProfit: int, optParSol: seq<int>) returns (optimalPartialSolution: seq<int>, profits:seq<int>)
  requires validProblem(jobs)
  requires 1 <= i < |jobs|
  requires |dp| == |allSol| == i
  requires |optParSol| == i
  requires isOptParSol(optParSol, jobs, i)
  requires dp[i - 1] == PartialSolProfit(optParSol, jobs, 0)
  requires forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, maxProfit, 0)
  requires forall partialSol :: |partialSol| == i  && isPartialSol(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, dp[i - 1], 0); //dp[i-1] profitul optim pentru job-urile de lungime i
  requires dp[i - 1] >= maxProfit
  ensures isPartialSol(optimalPartialSolution, jobs, i + 1)
  ensures isOptParSol(optimalPartialSolution, jobs, i + 1)
  ensures profits == dp + [dp[i-1]]
  ensures |profits| == i + 1
  ensures HasProfit(optimalPartialSolution, jobs, 0, profits[i])
  ensures forall partialSol :: |partialSol| == i + 1 && isPartialSol(partialSol, jobs, |partialSol|) ==> HasLessProf(partialSol, jobs, profits[i], 0);
{
  //demonstram ca dp[i - 1] este maxim folosindu-ne de ce stim de la pasul anterior (toate profiturile posibile <= dp[i-1] )
  //daca nu adaugam un job, profitul ramane acelasi cu cel anterior care este <= dp[i-1] ==> conditia se pastreaza dp[i] = dp[i-1]
  assert dp[i-1] >= maxProfit;

  profits := dp + [dp[i-1]]; //profitul maxim ramane profitul anterior deoarece prin prin selectarea job-ului curent nu se obtine un profit mai mare
  assert dp[i - 1] == PartialSolProfit(optParSol, jobs, 0);

  AssociativityOfProfitFunc(optParSol, jobs, 0, 0);
  optimalPartialSolution := optParSol + [0]; //solutia nu contine job-ul i deoarece se obtine un profit mai bun fara el
  assert dp[i - 1] == PartialSolProfit(optimalPartialSolution, jobs, 0);

  assert isPartialSol(optimalPartialSolution, jobs, i + 1);
  assert partialSolutionWithoutJobI(optimalPartialSolution, jobs, i);
  optimalPartialSolutionWithoutJobI(i, jobs, maxProfit, dp, profits);

  assert isOptParSol(optimalPartialSolution, jobs, i + 1);
  assert forall partialSol :: |partialSol| == i + 1 && isPartialSol(partialSol, jobs, |partialSol|) ==> HasLessProf(partialSol, jobs, profits[i], 0);
}


method WeightedJobScheduling(jobs: seq<Job>) returns (sol: seq<int>, profit : int)
  requires validProblem(jobs)
  ensures isSolution(sol, jobs)
  ensures isOptimalSolution(sol, jobs)
{
  var dp :seq<int> := [];
  var dp0 := jobs[0].profit; //profitul primului job
  dp := dp + [dp0];
  var solution : seq<int> := [1]; //solutia optima de lungime 1
  var i: int := 1;
  var allSol : seq<seq<int>> := []; //stocam toate solutiile partiale optime
  allSol := allSol + [[1]]; //adaugam solutia partiala optima de lungime 1

  assert |solution| == 1;
  assert |allSol[0]| == |solution|;
  assert 0 <= solution[0] <= 1;

  assert isPartialSol(solution, jobs, i);
  assert validJob(jobs[0]); //profit >=0
  assert isOptParSol(solution, jobs, i); //[1] solutia optima de lungime 1

  while i < |jobs|
    invariant 1 <= i <= |jobs|
    decreases |jobs| - i
    invariant i == |dp|
    invariant 1 <= |dp| <= |jobs|
    decreases |jobs| - |dp|
    invariant isPartialSol(solution, jobs, i)
    invariant |solution| == i
    invariant i == |allSol|
    decreases |jobs| - |allSol|
    decreases |jobs| - |allSol[i-1]|
    invariant isPartialSol(allSol[i-1], jobs, i)
    invariant HasProfit(solution, jobs, 0, dp[i - 1])
    invariant HasProfit(allSol[i - 1], jobs, 0 , dp[i - 1])
    invariant OptParSolutions(allSol, jobs, dp, i)
    invariant isOptParSol(allSol[i - 1], jobs, i)
    invariant forall partialSol :: |partialSol| == i  && isPartialSol(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, dp[i - 1], 0) //sol par optima
    invariant isOptParSol(solution, jobs, i)
  {
    var maxProfit, optParSolWithI := MaxProfitWithJobI(jobs, i, dp, allSol);

    assert maxProfit == PartialSolProfit(optParSolWithI, jobs, 0);
    assert partialSolutionWithJobI(optParSolWithI, jobs, i);
    assert forall partialSol :: |partialSol| == i + 1 && partialSolutionWithJobI(partialSol, jobs, i) ==> HasLessProf(partialSol, jobs, maxProfit, 0);
    //calculeaza maximul dintre excluded profit si included profit
    //maximul dintre profitul obtinut pana la job-ul anterior si profitul obtinut cu adugarea job-ului curent

    if dp[i-1] >= maxProfit //se obtine un profit mai bun fara job-ul curent //lemma requires conditia
    {

      solution, dp :=leadsToOptWithoutJobI(jobs, dp, allSol, i, maxProfit, solution);
      assert isOptParSol(solution, jobs, i + 1);

    }
    else //alegem job-ul i dp[i-1] < maxProfit
    {

      solution, dp := leadsToOptWithJobI(jobs, dp, allSol, i, maxProfit, optParSolWithI);
      assert isOptParSol(solution, jobs, i + 1);

    }
    allSol := allSol + [solution]; //cream secventa de solutii partiale optime(care includ job-ul curent sau nu) pentru fiecare job in parte
    //allSol[j] = contine solutia partiala optima pana la pozitia j inclusiv (formata din job-urile pana la pozitia j inclusiv, partiala optima)
    i := i + 1;
  }

  sol := solution;
  profit := dp[|dp|-1]; //ultimul profit este maxim
}

method Main()
{
  var job1: Job := Tuple(jobStart := 1, jobEnd := 2, profit := 50);
  var job2: Job := Tuple(jobStart := 3, jobEnd := 5, profit := 20);
  var job3: Job := Tuple(jobStart := 6, jobEnd := 19, profit := 100);
  var job4: Job := Tuple(jobStart := 2, jobEnd := 100, profit := 200);
  var jobs: seq<Job> := [job1, job2, job3, job4];
  // //secventa de job-uri trebuie sa fie valida (1)
  // //-----------------------------------contina job-uri diferite din pctdv al cel putin un timp (st sau sf)
  var solutie : seq<int> := [];
  var profit : int := 0;
  solutie, profit := WeightedJobScheduling(jobs);
  // print ("Solutia optima: ", solutie);
  // print ("Profitul maxim pentru secventa de job-uri: ", profit);
  print (solutie);
  print (profit);
  //solutia trebuie sa contina valori 0, 1 , sa fie de lungime |jobs|, job-uri care nu se suprapun si sa fie de profit maxim
  var m := map[4 := 5, 5 := 6];
  assert m[4] == 5;
  m := m[6 := 7];
  print(m);
}