function flatten<T(!new)>(nested: set<set<T>>) : (f: set<T>)
    ensures forall i :: i in nested ==> 
    (
        (i <= f) &&
        (forall j :: j in i ==> j in f)
    )
    ensures forall i :: i !in f ==>
    (
        forall j :: j in nested ==> i !in j
    )
{
    set x, y | y in nested && x in y :: x
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

function max(s: set<int>) : (m: int)
    requires |s| >= 1
    ensures m in s
    ensures forall i :: i in s ==> m >= i
{
    max_exists(s);
    var x :| x in s && forall y :: y in s ==> x >= y;
    x
}

lemma notempty<K,V>(s: set<K>, m: map<K,V>)
    requires s == m.Keys
    ensures |s| == |m|
    ensures |s| >= 1 ==> |m| >= 1
{}

function map_set<A(!new),B>(x: set<A>, f: (A) -> B) :  (y: set<B>)
    ensures |x| >= 1 ==> |y| >= 1
    ensures y == (set i | i in x :: f(i))
    ensures forall i :: i in x ==> f(i) in y
{
    var y := set i | i in x :: f(i);
    ghost var ys_map := map i | i in x :: f(i);
    assert x == ys_map.Keys;
    assert y == ys_map.Values;
    y
}