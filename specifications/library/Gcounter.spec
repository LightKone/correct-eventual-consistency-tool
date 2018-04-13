@type datatype
@name Gcounter

@content

type Gcounter = [int]int;
const unique replicas:int;

function inc(counter:Gcounter, oldCounter:Gcounter, replica:int) returns(bool)
{
  (forall i:int :: (i == replica ==> (counter[i] == oldCounter[i] + 1)) && (i != replica ==> (counter[i] == oldCounter[i])))
}

function value(counter:Gcounter) returns(int)
{
  sum(counter, 0)
}

function sum(counter:Gcounter, index:int) returns(int)
{
  (if (index < replicas) then (counter[index] + sum(counter, index + 1)) else 0)
}
function counterEquals(one:Gcounter, two:Gcounter) returns(bool)
{
  (forall i: int :: one[i] == two[i])
}
function counterReset(counter:Gcounter) returns(bool)
{
  (forall i:int :: counter[i] == 0)
}		 

@equals (forall i:int :: @this[i] == @other[i]);
