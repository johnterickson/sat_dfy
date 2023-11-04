module Map {
    import opened Seq
    
    ghost function map_sum_spec<T>(m: map<T,int>) : (sum: int)
        ensures Seq.seq_sum(map_vals_to_seq_spec(m)) == sum
    {
        if |m| == 0 then
            0
        else if |m| == 1 then
            var x := map_pick(m);
            m[x]
        else
            var x := map_pick(m);
            m[x] + map_sum_spec(m - {x})
    }

    ghost function map_pick<K,V>(m: map<K,V>) : (x: K)
        requires |m| != 0
        ensures x in m && x in m.Keys && m[x] in m.Values
    {
        var x :| x in m; x
    }

    ghost function map_vals_to_multiset<K,V>(m: map<K,V>) : (out: multiset<V>)
    {
        if |m| == 0 
        then multiset([])
        else 
            var k := map_pick(m);
            multiset([m[k]]) + map_vals_to_multiset(m - {k})
    }

    ghost function map_vals_to_seq_spec<K,V>(m: map<K,V>) : (out: seq<V>)
        ensures map_vals_to_multiset(m) == multiset(out)
    {
        if |m| == 0 
        then [] 
        else 
            var k := map_pick(m);
            [m[k]] + map_vals_to_seq_spec(m - {k})
    }

    method map_vals_to_seq<K,V>(m: map<K,V>) returns (out: seq<V>)
        decreases m
        ensures multiset(out) == multiset(map_vals_to_seq_spec(m))
    {
        if |m| == 0 {
            out := [];
        } else {
            var x :| x in m;
            var remaining := map_vals_to_seq(m - {x});
            out := [m[x]] + remaining;
        }
    }

    
    function map_sum<T>(m: map<T,int>) : (sum: int)
        decreases |m|
        ensures sum == map_sum_spec(m)
    {
        if |m| == 0 then
            0
        else
            var x := map_pick(m);
            m[x] + map_sum_spec(m - {x})
    }
    by method
    {
        var ss := map_vals_to_seq(m);
        DifferentPermutationSameSum(ss, map_vals_to_seq_spec(m));
        sum := seq_sum(ss);
    }
}