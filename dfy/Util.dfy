include "Map.dfy"
include "Seq.dfy"
include "Set.dfy"

module Util {
    import opened Map
    import opened Set
    import opened Seq

function max(a: int, b: int) : (m: int)
    ensures m >= a
    ensures m >= b
    ensures m == a || m == b
{
    if a >= b then a else b
}

}