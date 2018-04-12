@type datatype
@name Set


@content

type Set = <a>[a]bool;

function setAdd<a>(element:a, set: Set, oldSet: Set)returns(bool)
{
    (forall <b> e: b :: ((e != element) ==> (set[e] == oldSet[e])) && ((e == element) ==> (set[element] == true)))
}

function setRemove<a>(element:a, set: Set, oldSet: Set)returns(bool)
{
    (forall <b> e: b :: ((e != element) ==> (set[e] == oldSet[e])) && ((e == element) ==> (set[element] == false)))
}

function setIn<a>(element:a, set: Set)returns(bool)
{
    (set[element])
}

@equals forall <a> e: a :: @this[e] == @other[e];
