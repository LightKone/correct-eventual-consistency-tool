@type unit
@name Map2K


@content

function map2KSet<k1, k2, v>(key1: k1, key2 : k2, value: v, map: [k1, k2]v, oldMap: [k1, k2]v)returns(bool)
{
    (forall e1: k1, e2: k2 :: (((e1 != key1) || (e2 != key2)) ==> (map[e1, e2] == oldMap[e1, e2])) && ((e1 == key1) && (e2 == key2) ==> (map[key1, key2] == value)))
}

function map2KEquals<k1, k2, v>(this: [k1, k2]v, other: [k1, k2]v)returns(bool)
{
    (forall e1: k1, e2: k2 :: this[e1, e2] == other[e1, e2])
}
