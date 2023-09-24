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

lemma multiset_max_exists(s: multiset<int>)
    requires |s| >= 1
    ensures exists x :: x in s && forall y :: y in s ==> x >= y
{
    var max :| max in s;
    var visited := multiset{max};
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

        to_visit := to_visit - multiset{x};
        visited := visited + multiset{x};
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

function set_max(s: set<int>) : (m: int)
    requires |s| >= 1
    ensures m in s
    ensures forall i :: i in s ==> m >= i
{
    max_exists(s);
    var x :| x in s && forall y :: y in s ==> x >= y;
    x
}

// function multiset_max(s: multiset<int>) : (m: int)
//     requires |s| >= 1
//     ensures m in s
//     ensures forall i :: i in s ==> m >= i
// {
//     multiset_max_exists(s);
//     var x :| x in s && forall y :: y in s ==> x >= y;
//     x
// }

// function max4(a: int, b:int, c:int, d:int) : (m: int)
//     ensures m >= a
//     ensures m >= b
//     ensures m >= c
//     ensures m >= d
//     ensures m == a || m == b || m == c || m == d
// {
//     max(max(a,b),max(c,d))
// }

// function max3(a: int, b:int, c:int) : (m: int)
//     ensures m >= a
//     ensures m >= b
//     ensures m >= c
//     ensures m == a || m == b || m == c
// {
//     max(max(a,b),c)
// }

// ghost function merge_top_two(a: (int,int), b:(int,int)) : (c:(int,int))
//     requires a.0 >= a.1
//     requires b.0 >= b.1
//     ensures c.0 >= c.1
//     ensures c.0 == max4(a.0,a.1,b.0,b.1)
//     ensures c.1 == (if c.0 == a.0 then 
//         max3(a.1,b.0,b.1)
//     else if c.0 == a.1 then
//         max3(a.0,b.0,b.1)
//     else if c.0 == b.0 then
//         max3(a.0,a.1,b.1)
//     else
//         max3(a.0,a.1,b.0))
// {
//     var top := max4(a.0,a.1,b.0,b.1);
//     var second := if top == a.0 then 
//         max3(a.1,b.0,b.1)
//     else if top == a.1 then
//         max3(a.0,b.0,b.1)
//     else if top == b.0 then
//         max3(a.0,a.1,b.1)
//     else
//         max3(a.0,a.1,b.0);
//     (top, second)
// }

// function find_seq_max(s: seq<int>) : (i:int)
//     requires |s| >= 1
//     ensures 0 <= i < |s|
//     ensures forall ii :: 0 <= ii < |s| ==> s[i] >= s[ii]
// {
//     if |s| == 1 then
//         0
//     else
//         var e := |s|-1;
//         var i := find_seq_max(s[0..e]);
//         if s[e] > s[i] then
//             e
//         else
//             i
// }

lemma SecondHasAtMostOneThatIsBigger(s: seq<int>, m:(int,int))
    requires |s| >= 2
    requires 0 <= m.0 < |s|
    requires 0 <= m.1 < |s|
    requires forall ii :: 0 <= ii < |s| ==> s[m.0] >= s[ii]
    requires forall ii :: 0 <= ii < |s| ==> ii == m.0 || s[m.1] >= s[ii]
    requires forall ii :: 0 <= ii < |s| && ii != m.0 ==> s[m.1] >= s[ii]
    ensures |set i | 0 <= i < |s| && s[i] > s[m.1]| <= 1
{
    var i := 0;
    var visited : set<int> := {};
    var bigger : set<int> := {};
    while i != |s|
        invariant 0 <= i <= |s|
        invariant visited == (set ii {:trigger true} | 0 <= ii < i)
        invariant bigger == (set ii | 0 <= ii < i && s[ii] > s[m.1])
        invariant |bigger| <= 1
        decreases |s| - i
    {
        if s[i] > s[m.1] {
            bigger := bigger + {i};
        }
        visited := visited + {i};
        i := i + 1;
    }
    assert i == |s|;
    assert visited == (set ii {:trigger true} | 0 <= ii < |s|);
}

function find_indices_of_top_two(s: seq<int>) : (i:(int,int))
    requires |s| >= 2
    ensures 0 <= i.0 < |s|
    ensures 0 <= i.1 < |s|
    ensures i.0 != i.1
    ensures s[i.0] >= s[i.1]
    ensures s[i.0] == s[i.1] ==>
        forall ii :: 0 <= ii < |s| ==> s[i.0] >= s[ii] && s[i.1] >= s[ii]
    ensures s[i.0] != s[i.1] ==>
        forall ii :: 0 <= ii < |s| ==> s[i.0] >= s[ii]
    ensures s[i.0] != s[i.1] ==>
        forall ii :: 0 <= ii < |s| ==> ii == i.0 || s[i.1] >= s[ii]
{
    var i := if |s| == 2 then
        if s[0] >= s[1] then (0,1) else (1,0)
    else
        var e := |s|-1;
        var i := find_indices_of_top_two(s[0..e]);
        if s[e] > s[i.0] then
            (e,i.0)
        else if s[e] > s[i.1] then
            (i.0,e)
        else
            (i.0,i.1);
    SecondHasAtMostOneThatIsBigger(s, i);
    i
}

function merge_top_two(a:(int,int), b:(int,int)) : (m:(int,int))
    requires a.0 >= a.1
    requires b.0 >= b.1
    ensures m.0 >= m.1
    ensures m == top_two([a.0, a.1, b.0, b.1])
    // ensures
    //     var s := [a.0, a.1, b.0, b.1];
    //     var i := find_indices_of_top_two(s);
    //     m.0 == s[i.0] && m.1 == s[i.1] &&
    //     (forall ii :: 0 <= ii < |s| ==> s[i.0] >= s[ii]) &&
    //     (forall ii :: 0 <= ii < |s| ==> ii == i.0 || s[i.1] >= s[ii]) &&
    //     (forall ii :: 0 <= ii < |s| && ii != i.0 ==> s[i.1] >= s[ii]) &&
    //     |set ii | 0 <= ii < |s| && s[ii] > s[i.1]| <= 1
{
    var s := [a.0, a.1, b.0, b.1];
    var i := find_indices_of_top_two(s);
    var m := (s[i.0],s[i.1]);
    assert m.0 == s[i.0] && m.1 == s[i.1];
    m
}

function top_two(s: seq<int>) : (m:(int,int))
    requires |s| >= 2
    ensures m.0 in s
    ensures m.1 in s
    ensures m.0 >= m.1
    ensures
        var i := find_indices_of_top_two(s);
        (m.0 == s[i.0]) &&
        (m.1 == s[i.1]) &&
        (m.0 == m.1 ==>
            forall ii :: 0 <= ii < |s| ==> m.0 >= s[ii] && m.1 >= s[ii]) &&
        (m.0 != m.1 ==>
            forall ii :: 0 <= ii < |s| ==> m.0 >= s[ii]) &&
        (m.0 != m.1 ==>
            forall ii :: 0 <= ii < |s| ==> ii == i.0 || m.1 >= s[ii])
{
    var i := find_indices_of_top_two(s);
    (s[i.0], s[i.1])
}

// function top_two(s: seq<int>) : (m:(int,int))
//     requires |s| >= 2
//     ensures forall i :: i in s ==> m.0 >= i
//     ensures forall i :: i in s ==> m.1 == m.0 || m.1 >= i
// {
//     var top_i := find_seq_max(s);
//     var rest := s[0..top_i] + s[(top_i+1)..];
//     var second_i := find_seq_max(rest);
//     var second_i := second_i + if second_i >= top_i then 1 else 0;
//     (s[top_i], s[second_i])
// }

