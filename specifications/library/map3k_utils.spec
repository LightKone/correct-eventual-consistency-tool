@type unit
@name Map3K


@content

function map3KSet<k1, k2, k3, v>(key1: k1, key2: k2, key3: k3, value: v, map: [k1, k2, k3]v, oldMap: [k1, k2, k3]v)returns(bool)
{
    (forall e1: k1, e2: k2, e3: k3 :: (((e1 != key1) || (e2 != key2) || (e3 != key3)) ==> (map[e1, e2, e3] == oldMap[e1, e2, e3])) && ((e1 == key1) && (e2 == key2) && (e3 == key3) ==> (map[key1, key2, key3] == value)))
}

function map3KEquals<k1, k2, k3, v>(this: [k1, k2, k3]v, other: [k1, k2, k3]v)returns(bool)
{
    (forall e1: k1, e2: k2, e3: k3 :: this[e1, e2, e3] == other[e1, e2, e3])
}
