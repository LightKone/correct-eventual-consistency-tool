@type datatype
@name AddWinsSet


@content

type AddWinsSetSelector;
const unique AddWinsSetAdd: AddWinsSetSelector;
const unique AddWinsSetRemove: AddWinsSetSelector;
axiom(forall s:AddWinsSetSelector :: s == AddWinsSetAdd || s == AddWinsSetRemove);

type AddWinsSetElement = <a>[a]bool;
type AddWinsSet = [AddWinsSetSelector]AddWinsSetElement;

function add<a>(element:a, set: AddWinsSet, oldSet: AddWinsSet)returns(bool)
{
    (forall <b> e: b :: ((e != element) ==> (set[AddWinsSetAdd][e] == oldSet[AddWinsSetAdd][e])) && ((e == element) ==> (set[AddWinsSetAdd][element] == true)))
    && (forall <b> e: b :: (set[AddWinsSetRemove][e] == oldSet[AddWinsSetRemove][e]))
}

function remove<a>(element:a, set: AddWinsSet, oldSet: AddWinsSet)returns(bool)
{
    (forall <b> e: b :: ((e != element) ==> (set[AddWinsSetRemove][e] == oldSet[AddWinsSetRemove][e])) && ((e == element) ==> (set[AddWinsSetRemove][element] == true)))
    && (forall <b> e: b :: (set[AddWinsSetAdd][e] == oldSet[AddWinsSetAdd][e]))
}

function inSet<a>(element:a, set: AddWinsSet)returns(bool)
{
    (set[AddWinsSetAdd][element])
}

function isEmptySet(set:AddWinsSet) returns(bool)
{
    (forall <b> e:b :: (set[AddWinsSetAdd][e] == false) && (set[AddWinsSetRemove][e] == false))
}
function setequals(one:AddWinsSet, two:AddWinsSet) returns(bool)
{
  (forall <b> e: b :: (one[AddWinsSetRemove][e] == two[AddWinsSetRemove][e]) && (one[AddWinsSetAdd][e] == two[AddWinsSetAdd][e]))
}	

@equals forall <b> s: AddWinsSetSelector, e: b :: @this[s][e] == @other[s][e];
