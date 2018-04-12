@type datatype
@name RemWinsSet


@content

type RemWinsSetSelector;
const unique RemWinsSetAdd: RemWinsSetSelector;
const unique RemWinsSetRemove: RemWinsSetSelector;
axiom(forall s:RemWinsSetSelector :: s == RemWinsSetAdd || s == RemWinsSetRemove);

type RemWinsSetElement = <a>[a]bool;
type RemWinsSet = [RemWinsSetSelector]RemWinsSetElement;

function remWinsSetAdd<a>(element:a, set: RemWinsSet, oldSet: RemWinsSet)returns(bool)
{
    (forall <b> e: b :: ((e != element) ==> (set[RemWinsSetAdd][e] == oldSet[RemWinsSetAdd][e])) && ((e == element) ==> (set[RemWinsSetAdd][element] == true)))
    && (forall <b> e: b :: (set[RemWinsSetRemove][e] == oldSet[RemWinsSetRemove][e]))
}

function remWinsSetRemove<a>(element:a, set: RemWinsSet, oldSet: RemWinsSet)returns(bool)
{
    (forall <b> e: b :: ((e != element) ==> (set[RemWinsSetRemove][e] == oldSet[RemWinsSetRemove][e])) && ((e == element) ==> (set[RemWinsSetRemove][element] == true)))
    && (forall <b> e: b :: (set[RemWinsSetAdd][e] == oldSet[RemWinsSetAdd][e]))
}

function remWinsSetIn<a>(element:a, set: RemWinsSet)returns(bool)
{
    (set[RemWinsSetAdd][element] && !set[RemWinsSetRemove][element])
}

@equals forall <b> s: RemWinsSetSelector, e: b :: @this[s][e] == @other[s][e];
