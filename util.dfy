function flatten<T(!new)>(nested: set<set<T>>) : (f: set<T>)
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

lemma max_exists(s: set<int>)
    requires |s| >= 1
    ensures exists x :: x in s && forall y :: y in s ==> x >= y
{
    var max :| max in s;
    var visited := {max};
    var to_visit := s - visited;

    while |to_visit| > 0
        decreases |to_visit|
        invariant forall x :: x in visited ==> max >= x
        invariant visited + to_visit == s
        invariant max in s
    {
        var x :| x in to_visit;
        if x >= max {
            max := x;
        }

        to_visit := to_visit - {x};
        visited := visited + {x};
    }

    assert forall x :: x in visited ==> max >= x;
    assert visited == s;
    assert forall x :: x in s ==> max >= x;
}

lemma NotEmptySetHasNotEmptyMapping<A,B>(s: set<A>, f: (A) -> B, m: set<B>)
    requires |s| >= 1
    requires m == set i | i in s :: f(i)
    ensures |m| >= 1
{
    var i :| i in s;
    var y := f(i);
    assert y in m;
}


lemma notempty<K,V>(s: set<K>, m: map<K,V>)
    requires s == m.Keys
    ensures |s| == |m|
    ensures |s| >= 1 ==> |m| >= 1
{}

function map_not_empty<A(!new),B>(xs: set<A>, m: map<A,B>):  (ys: set<B>)
    requires xs == m.Keys
    ensures ys == m.Values
    ensures |xs| >= 1 ==> |ys| >= 1
    ensures forall x :: true ==> (x in xs <==> x in m.Keys && m[x] in ys)
{
    m.Values
}
