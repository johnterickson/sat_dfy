
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

    
    lemma EverythingEqualInSetOfOne<T>(s: set<T>, i: T)
        requires i in s
        requires |s| == 1
        ensures forall ii :: ii in s ==> i == ii
    {
        var to_check := s;
        var checked := {};
        while |to_check| > 0
            invariant to_check + checked == s
            invariant forall ii :: ii in checked ==> i == ii
        {
            var ii :| ii in to_check;

            to_check := to_check - {ii};
            checked := checked + {ii};
        }
    }

    function extract_only_from_set<T>(s: set<T>) : (out: T)
        requires |s| == 1
        ensures {out} == s
    {
        assert (
            ghost var i :| i in s;
            EverythingEqualInSetOfOne(s, i);
            forall ii :: ii in s ==> ii == i
        );
        var out :| out in s && forall i :: i in s ==> i == out;
        out
    }

    lemma ExistsMax<T>(m: map<T,int>)
        requires |m| > 0
        requires forall i1, i2 :: i1 in m && i2 in m && i1 != i2 ==> m[i1] != m[i2]
        ensures exists out :: out in m && forall i :: i in m && i != out ==> m[out] > m[i]
    {
        var max_key :| max_key in m.Keys;
        var max := m[max_key];
        var to_check := m.Keys - {max_key};
        var smaller := {};
        while |to_check| > 0
            invariant to_check + {max_key} + smaller == m.Keys
            invariant max == m[max_key]
            invariant max_key !in smaller
            invariant max_key !in to_check
            invariant forall i :: i in smaller ==> max > m[i]
        {
            var k :| k in to_check;
            if m[k] > max {
                smaller := smaller + { max_key };
                max_key := k;
                max := m[k];
            } else {
                smaller := smaller + { k };
            }
            to_check := to_check - { k };
        }
        assert max_key in m;
        assert forall i :: i in m ==> 
            if i == max_key then m[max_key] == m[i] else m[max_key] > m[i];
    }

    function extract_max_from_map<T>(m: map<T,int>) : (out: T)
        requires |m| > 0
        requires forall i1, i2 :: i1 in m && i2 in m && i1 != i2 ==> m[i1] != m[i2]
        ensures out in m
        ensures forall i :: i in m && i != out ==> m[out] > m[i]
    {
        ExistsMax(m);
        var out :| out in m && forall i :: i in m && i != out ==> m[out] > m[i];
        out
    }

    //(int, bool) -> realzz
    function extract_max_from_set_by_score<T>(s: set<T>, f: (T) -> int) : (out: T)
        requires |s| > 0
        requires forall i1, i2 :: i1 in s && i2 in s && i1 != i2 ==> f(i1) != f(i2)
        ensures out in s
        ensures forall i :: i in s && i != out ==> f(out) > f(i)
    {
        var m: map<T,int> := map i | i in s :: f(i);
        assert s == m.Keys;
        extract_max_from_map(m)
    }

    ghost predicate well_ordered<T(!new)>(s: set<T>, less_than: (T, T) -> bool)
    {
        (forall i1 :: i1 in s ==> !less_than(i1,i1)) &&
        (forall i1, i2 :: i1 in s && i2 in s && less_than(i1,i2) == !less_than(i2,i1)) && 
        (forall i1, i2, i3 :: i1 in s && i2 in s && i3 in s && less_than(i1,i2) && less_than(i2,i3) ==> less_than(i1,i3))
    }

    lemma ExistsMaxSorted<T(!new)>(s: set<T>, less_than: (T,T) -> bool)
        requires |s| > 0
        requires well_ordered(s, less_than)
        ensures exists max :: max in s && forall i :: i in s && i != max ==> less_than(i, max)
    {
        var max :| max in s;
        var to_check := s - {max};
        var smaller := {};
        while |to_check| > 0
            invariant to_check + {max} + smaller == s
            invariant max !in smaller
            invariant max !in to_check
            invariant forall i :: i in smaller ==> less_than(i, max)
        {
            var k :| k in to_check;
            if less_than(max, k) {
                assert forall i :: i in smaller ==> less_than(i, max);
                assert forall i :: i in smaller ==> less_than(i, k);
                smaller := smaller + { max };
                max := k;
            } else {
                smaller := smaller + { k };
            }
            to_check := to_check - { k };
        }

        assert {max} + smaller == s;
        assert forall i :: i in s && i != max ==> less_than(i, max);
    }

    function extract_max_from_set_by_order<T(!new)>(s: set<T>, less_than: (T,T) -> bool) : (out: T)
        requires |s| > 0
        requires well_ordered(s, less_than)
        ensures out in s
        ensures forall i :: i in s && i != out ==> less_than(i, out)
    {
        if |s| == 1 then
            extract_only_from_set(s)
        else
            ExistsMaxSorted(s, less_than);
            var max :| max in s && (forall j :: j in s && j != max ==> less_than(j,max));
            max
    }
}