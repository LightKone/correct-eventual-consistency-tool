@type unit
@name Map1K


@content

function map1KSet<k, v>(key: k, value: v, map: [k]v, oldMap: [k]v)returns(bool)
{
    (forall e: k :: ((e != key) ==> (map[e] == oldMap[e])) && ((e == key) ==> (map[key] == value)))
}

function map1KEquals<k, v>(this: [k]v, other: [k]v)returns(bool)
{
    (forall e: k :: this[e] == other[e])
}