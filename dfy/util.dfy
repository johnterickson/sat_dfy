
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

    ghost function set_to_seq_spec(s:set<int>) : (out: seq<int>)
        ensures multiset(s) == multiset(out)
    {
        if s == {} 
        then [] 
        else 
            var x := set_pick(s);
            [x] + set_to_seq_spec(s - {x})
    }

    method set_to_seq(s:set<int>) returns (out: seq<int>)
        decreases s
        ensures multiset(s) == multiset(out)
        ensures multiset(out) == multiset(set_to_seq_spec(s))
    {
        if s == {} {
            out := [];
        } else {
            var x :| x in s;
            var remaining := set_to_seq(s - {x});
            out := [x] + remaining;
        }
    }

    ghost function set_pick(s: set<int>) : (x: int)
        requires s != {}
    {
        var x :| x in s; x
    }

    function seq_sum(s: seq<int>) : (sum: int)
    {
        if s == [] then
            0
        else
            var x := s[0];
            var remaining := s[1..];
            x + seq_sum(remaining)
    }

    lemma MultiSetAdd(s1: multiset<int>, s2: multiset<int>, add: int)
        requires s1 + multiset([add]) == s2 + multiset([add])
        ensures s1 == s2
    {
        var added1 := s1 + multiset([add]);
        var removed1 := added1 - multiset([add]);
        assert s1 == removed1;
        var added2 := s2 + multiset([add]);
        var removed2 := added2 - multiset([add]);
        assert s2 == removed2;
    }

    lemma SeqPartsSameSum(s: seq<int>, s1: seq<int>, s2: seq<int>)
        requires s == s1 + s2
        ensures seq_sum(s) == seq_sum(s1) + seq_sum(s2)
    {
        if s == [] {
            assert s1 == [];
            assert s2 == [];
        } else if s1 == [] {
            assert s2 == s;
        } else {
            var x := s1[0];
            var s1' := s1[1..];
            assert s == [x] + s1' + s2;
            SeqPartsSameSum(s[1..], s1[1..], s2);
        }
    }

    lemma DifferentPermutationSameSum(s1: seq<int>, s2: seq<int>)
        requires multiset(s1) == multiset(s2)
        ensures seq_sum(s1) == seq_sum(s2)
    {
        if s1 == [] {
            assert s2 == [];
        } else {
            var x :| x in s1;
            assert x in s1;
            assert multiset(s1)[x] > 0;
            assert multiset(s2)[x] > 0;
            assert x in s2;
            var i1, i2 :| 0 <= i1 < |s1| && 0 <= i2 < |s2| && s1[i1] == s2[i2] && s1[i1] == x;

            var remaining1 := s1[..i1] + s1[i1+1..];
            assert s1 == s1[..i1] + s1[i1..];
            assert s1 == s1[..i1] + [x] + s1[i1+1..];
            assert seq_sum(s1) == seq_sum(s1[..i1] + [x] + s1[i1+1..]);
            SeqPartsSameSum(s1[..i1+1], s1[..i1], [x]);
            SeqPartsSameSum(s1, s1[..i1+1], s1[i1+1..]);
            assert seq_sum(s1) == seq_sum(s1[..i1]) + x + seq_sum(s1[i1+1..]);
            SeqPartsSameSum(remaining1, s1[..i1], s1[i1+1..]);
            assert multiset(s1) == multiset(remaining1 + [x]);
            assert seq_sum(s1) == seq_sum(remaining1) + x;
            assert multiset(s1) == multiset(remaining1) + multiset([x]);
            assert multiset(s1) - multiset([x]) == multiset(remaining1);

            var remaining2 := s2[..i2] + s2[i2+1..];
            assert s2 == s2[..i2] + s2[i2..];
            assert s2 == s2[..i2] + [x] + s2[i2+1..];
            assert seq_sum(s2) == seq_sum(s2[..i2] + [x] + s2[i2+1..]);
            SeqPartsSameSum(s2[..i2+1], s2[..i2], [x]);
            SeqPartsSameSum(s2, s2[..i2+1], s2[i2+1..]);
            assert seq_sum(s2) == seq_sum(s2[..i2]) + x + seq_sum(s2[i2+1..]);
            SeqPartsSameSum(remaining2, s2[..i2], s2[i2+1..]);
            assert multiset(s2) == multiset(remaining2 + [x]);
            assert seq_sum(s2) == seq_sum(remaining2) + x;
            assert multiset(s2) == multiset(remaining2) + multiset([x]);
            assert multiset(s2) - multiset([x]) == multiset(remaining2);

            DifferentPermutationSameSum(remaining1, remaining2);
            assert seq_sum(remaining1) == seq_sum(remaining2);
            assert seq_sum(s1) == seq_sum(s2);
        }
    }

    ghost function set_sum_spec(s: set<int>) : (sum: int)
        ensures seq_sum(set_to_seq_spec(s)) == sum
    {
        if s == {} then
            0
        else
            var x := set_pick(s);
            x + set_sum_spec(s - {x})
    }

    method set_sum(s: set<int>) returns (sum: int)
        decreases |s|
        ensures sum == set_sum_spec(s)
    {
        var ss := set_to_seq(s);
        DifferentPermutationSameSum(ss, set_to_seq_spec(s));
        sum := seq_sum(ss);
    }

    lemma SumTests()
    {
        assert set_sum_spec({}) == 0;
        assert set_sum_spec({1}) == 1;
        assert set_sum_spec({1,2}) == 3;
        assert set_sum_spec({1,2,3}) == 6;
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