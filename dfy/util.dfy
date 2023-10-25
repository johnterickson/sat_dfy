
module Util {
    function flatten_set<T(!new)>(nested: set<set<T>>) : (f: set<T>)
        ensures forall n :: n in nested ==> 
        (
            (n <= f) &&
            (forall i :: i in n ==> i in f)
        )
        ensures forall i :: i !in f ==>
        (
            forall j :: j in nested ==> i !in j
        )
        ensures forall i :: i in f ==>
        (
            exists j :: j in nested && i in j
        )
        ensures forall i :: true ==> (
            i in f
                <==>
            exists n :: n in nested && i in n
        )
    {
        set x, y | y in nested && x in y :: x
    }

    function max(a: int, b: int) : (m: int)
        ensures m >= a
        ensures m >= b
        ensures m == a || m == b
    {
        if a >= b then a else b
    }
}