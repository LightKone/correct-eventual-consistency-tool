@type datatype
@name Gset

@content

type Gset = <a>[a]bool;

function gsetAdd<a>(element:a, set:Gset, oldSet:Gset) returns(bool)
{
  (forall b:a :: ((b == element) ==> (set[b] == true)) && ((b != element) ==> (set[b] == oldSet[b])))
}	
function gsetContains<a>(element:a, set:Gset) returns(bool)
{
  (set[element])
}	
function gsetEquals(one:Gset, two:Gset) returns(bool)
{
  (forall <a> e:a :: (one[e] == two[e]))
}
function gsetEmpty(set:Gset) returns(bool)
{
  !(exists <a> e:a :: set[e])
}

@equals (forall <a> e:a :: @this[e] == @other[e]);
