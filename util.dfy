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

function pick(s: set<int>): (x: int)
  requires s != {}
  ensures |s| == 1 ==> {x} == s
{
    var x :| x in s; 
    assert x in s;
    if |s| == 1 then 
        var remainder := s - {x};
        assert |remainder| == 0;
        assert remainder == {};
        assert remainder + {x} == s;
        assert {x} == s;
        x
    else
        x
}

function max(s: set<int>) : (m: int)
    requires |s| >= 1
    decreases s
    ensures m in s
    ensures forall i :: i in s ==> m >= i
{
    var x := pick(s);
    if |s| == 1 then
        assert forall i :: i in s ==> x >= i;
        x
    else 
        var remainder := s - {x};
        var y:int := max(remainder);
        if (x >= y) then 
            assert forall i :: i in remainder ==> y >= i;
            assert forall i :: i in remainder ==> x >= i;
            assert s == {x} + remainder;
            assert forall i :: i in s ==> x >= i;
            x
        else 
            assert forall i :: i in s ==> y >= i;
            y
}

lemma notempty<K,V>(s: set<K>, m: map<K,V>)
    requires s == m.Keys
    ensures |s| == |m|
    ensures |s| >= 1 ==> |m| >= 1
{}