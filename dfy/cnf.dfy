include "sat.dfy"

// Clause: l1 ∨ l2 ∨ ... ∨ ln
// CNF: C1 ∧ C2 ∧ ... ∧ Cn

module CNF {
    import opened SAT

function clause_is_tautology(c: Clause) : (out: bool)
    ensures out ==> (
        forall vs: map<Variable,bool> :: true ==> clause_eval(c, vs) == true
    )
{
    exists l1,l2 :: l1 in c && l2 in c && l1.invert() == l2
}

ghost function cnf_equivalent(cnf: CNF, other: CNF) : (eq: bool)
{
    forall vs : map<Variable, bool> :: true ==>
        cnf_eval(cnf,vs) == cnf_eval(other, vs)
}

ghost function cnf_implies(cnf: CNF, other: CNF) : (eq: bool)
{
    forall vs : map<Variable, bool> :: true ==>
        (cnf_eval(cnf,vs) ==> cnf_eval(other, vs))
}

predicate cnf_has_tautologies(cnf: CNF)
{
    exists c :: c in cnf && clause_is_tautology(c)
}

function cnf_remove_tautologies(cnf: CNF) : (out: CNF)
    ensures cnf_equivalent(cnf, out)
    ensures !cnf_has_tautologies(out)
{
    set c | c in cnf && !clause_is_tautology(c)
}

function clause_max_litvar(c: Clause) : (out: ClauseLit)
    requires |c| > 0
{
    var lambda := (l: ClauseLit) => l.number();
    SAT.NumbersBijection(c, lambda);
    Util.extract_max_from_set_by_score(c, lambda)
}

function clause_lt(c1: Clause, c2: Clause) : (out: bool)
    requires c1 != c2
{
    if |c1| < |c2| then
        true
    else if |c1| > |c2| then
        false
    else
        var l1 := clause_max_litvar(c1);
        var l2 := clause_max_litvar(c2);
        if l1.number() < l2.number() then
            true
        else if l1.number() > l2.number() then
            false
        else
            assert l1 == l2;
            assert c1 - {l1} + {l1} == c1;
            clause_lt(c1 - {l1}, c2 - {l2})
}

// lemma WellFormed(s: set<Clause>)
//     ensures Util.well_ordered(s, (c1,c2) => clause_lt(c1,c2))
// {

// }

// function max_clause(cnf: CNF) : (out: Clause)
//     requires |cnf| > 0
// {
//     Util.extract_max_from_set_by_order(cnf, clause_lt)
// }

// function cnf_find_resolution_with_var(cnf: CNF, v: Variable) : (out: set<Clause>)
//     requires !cnf_has_tautologies(cnf)
//     // ensures (exists l1, l2, c1, c2 ::
//     //     v in cnf_vars(cnf) &&
//     //     c1 in cnf && c2 in cnf && c1 != c2 &&
//     //     l1 in c1 && NotInverted(v) == l1 &&
//     //     l2 in c2 && Inverted(v) == l2) <==> |out| == 2
//     ensures |out| == 0 || |out| == 2
// {
//     var where_inverted := set c | c in cnf && Inverted(v) in c;
//     var where_not_inverted := set c | c in cnf && NotInverted(v) in c;
//     assert |where_inverted * where_not_inverted| == 0;
//     if |where_inverted| > 0 && |where_not_inverted| > 0 then
//         var c1 :| c1 in where_inverted && forall c :: c in where_inverted && c != c1 && c1 > c;
//         var c2 :| c2 in where_not_inverted;
//         {c1, c2}
//     else
//         {}
// }

ghost function cnf_resolution_vars(cnf: CNF) : (out: set<Variable>)
    ensures forall v :: v in out <==> v in cnf_vars(cnf) && cnf_has_resolution_with_var(cnf, v)
{
    set v | v in cnf_vars(cnf) && cnf_has_resolution_with_var(cnf, v)
}

function cnf_has_resolution(cnf: CNF) : (out: bool)
    ensures out == (exists v :: v in cnf_vars(cnf) && cnf_has_resolution_with_var(cnf, v))
{
    exists v :: v in cnf_vars(cnf) && cnf_has_resolution_with_var(cnf, v)
}

function cnf_has_resolution_with_var(cnf: CNF, v: Variable) : (out: bool)
{
    exists c1, c2 ::
        v in cnf_vars(cnf) &&
        c1 in cnf && c2 in cnf && c1 != c2 &&
        NotInverted(v) in c1 &&
        Inverted(v) in c2
}

lemma BasicResolution(p: bool, q: bool, r: bool)
    ensures ((p || q) && (!p || r)) ==> (q || r)
{
    
}

function merge_resolution_specific(v: Variable, vs: map<Variable, bool>, c1: Clause, c2: Clause) : (out: Clause)
    requires v in vs
    requires NotInverted(v) in c1 && Inverted(v) in c2
    ensures (clause_eval(c1, vs) && clause_eval(c2, vs)) ==> clause_eval(out, vs)
    ensures cnf_implies({c1, c2}, {out})
{
    var c1_others := c1 - {NotInverted(v)};
    var c2_others := c2 - {Inverted(v)};
    c1_others + c2_others
}

// function merge_resolution(v: Variable, c1: Clause, c2: Clause) : (out: Clause)
//     requires NotInverted(v) in c1 && Inverted(v) in c2
//     ensures cnf_equivalent({c1, c2}, {out})
// {
//     var orig := {c1, c2};

//     var c1_others := c1 - {NotInverted(v)};
//     assert forall vs :: v in vs ==> 
//         clause_eval(c1, vs) == if vs[v] then
//              true
//         else
//             clause_eval(c1_others, vs);
//     assert forall vs :: v in vs ==> 
//         clause_eval(c1, vs) == (vs[v] || clause_eval(c1_others, vs));

//     var c2_others := c2 - {Inverted(v)};
//     assert forall vs :: v in vs ==> 
//         clause_eval(c2, vs) == if vs[v] then
//              clause_eval(c2_others, vs)
//         else
//             true;
//     assert forall vs :: v in vs ==> 
//         clause_eval(c2, vs) == (!vs[v] || clause_eval(c2_others, vs));

//     assert forall vs :: v in vs ==>
//         BasicResolution(vs[v], clause_eval(c1_others, vs), clause_eval(c2_others, vs));
//         assert (v[s] || clause_eval(c1_others, vs)) && (!v[s] || clause_eval(c2_others, vs)) == (clause_eval(c1_others, vs) || clause_eval(c2_others, vs));

//     // assert forall vs :: v in vs ==> 
//     //     if vs[v] then
//     //         clause_eval(c1, vs) == 
//     assert forall vs :: v in vs ==> 
//         if vs[v] then
//             cnf_eval(orig, vs) == cnf_eval({c2}, vs)
//         else
//             cnf_eval(orig, vs) == cnf_eval({c1}, vs);

//     assert forall vs :: v in vs ==> 
//         if vs[v] then
//             cnf_eval(orig, vs) == cnf_eval({c2_others}, vs)
//         else
//             cnf_eval(orig, vs) == cnf_eval({c1_others}, vs);

//     assert forall vs :: v in vs ==> 
//         cnf_eval(orig, vs) ==
//             if vs[v] then
//                 cnf_eval({c2_others}, vs)
//             else
//                 cnf_eval({c1_others}, vs);

//     assert forall vs :: v in vs ==> 
//         cnf_eval(orig, vs) ==
//             if vs[v] then
//                 clause_eval(c2_others, vs)
//             else
//                 clause_eval(c1_others, vs);
    
//     assert forall vs :: v in vs ==> 
//         cnf_eval(orig, vs) ==
//             (clause_eval(c2_others, vs) || clause_eval(c1_others, vs));

//     // assert forall vs :: v in vs ==> 
//     //     cnf_eval(orig, vs) == (clause_eval(c1, vs) && clause_eval(c2, vs));
        
//     // assert forall vs :: v in vs ==> 
//     //     (   cnf_eval(orig, vs) == cnf_eval({c1_others}, vs) 
//     //      || cnf_eval(orig, vs) == cnf_eval({c2_others}, vs));

//     // assert forall vs :: v in vs ==> 
//     //     cnf_eval(orig, vs) == cnf_eval({c1_others + c2_others}, vs);

//     assert forall vs :: v in vs ==>
//         (clause_eval(c1_others, vs) || clause_eval(c2_others, vs)) == clause_eval(c1_others + c2_others, vs);


//     assert forall vs :: v in vs ==> 
//         cnf_eval(orig, vs) == cnf_eval({c1_others + c2_others}, vs);
        
//     var merged := c1_others + c2_others;
//     merged
// }

// ghost function cnf_some_resolution_var(cnf: CNF) : (v: Variable)
//     requires cnf_has_resolution(cnf)
//     ensures exists l1, l2, c1, c2 ::
//         c1 in cnf && c2 in cnf && c1 != c2 &&
//         l1 in c1 && NotInverted(v) == l1 &&
//         l2 in c2 && Inverted(v) == l2
// {
//     assert exists v :: v in cnf_vars(cnf) && cnf_has_resolution_with_var(cnf, v);
//     var v :| v in cnf_vars(cnf) && cnf_has_resolution_with_var(cnf, v);
//     v
// }

// function cnf_clauses_with_var(cnf: CNF, ls: set<ClauseLit>) : (out: set<Clause>)
//     ensures forall c :: c in cnf && (exists l :: l in ls && l in c) <==> c in out
// {
//     set c | c in cnf && (exists l :: l in ls && l in c)
// }

lemma SetSetWithSomethingInItIsNotEmpty<T>(s: set<T>, f: T -> bool, ss: set<T>)
    requires exists x :: x in s && f(x)
    requires ss == set x | x in s && f(x)
    ensures |ss| > 0
{
    var x :| x in s && f(x);
    assert x in s;
    assert f(x);
    assert x in ss;
    assert |ss| > 0;
}

function cnf_resolution(cnf: CNF) : (out: CNF)
    requires !cnf_has_tautologies(cnf)
    ensures !cnf_has_resolution(out)
    ensures cnf_equivalent(cnf, out)
{
    // no tautologies
    assert forall v, l1, l2, c ::
        v in cnf_vars(cnf) &&
        c in cnf &&
        l1 in c && l2 in c ==>
            l1.invert() != l2;

    var resolutions: set<(Variable, Clause, Clause)> := set v,c1,c2 
        | v in cnf_vars(cnf) && c1 in cnf && c2 in cnf && c1 != c2 &&
            NotInverted(v) in c1 && Inverted(v) in c2
        :: (v, c1, c2);
    assert forall r :: r in resolutions ==> (
        assert r.0 in cnf_vars(cnf);
        assert exists c1, c2 :: 
            r.0 in cnf_vars(cnf) &&
            c1 in cnf && c2 in cnf && c1 != c2
            && NotInverted(r.0) in c1 && Inverted(r.0) in c2;

        cnf_has_resolution_with_var(cnf, r.0)
        );
    
    assume false;
    cnf
}

// function cnf_resolution(cnf: CNF) : (out: CNF)
//     requires !cnf_has_tautologies(cnf)
//     requires cnf_has_resolution(cnf)
//     ensures cnf_equivalent(cnf, out)
// {
//     var v := cnf_some_resolution_var(cnf);
//     assert exists l1, l2, c1, c2 ::
//         c1 in cnf && c2 in cnf && c1 != c2 &&
//         l1 in c1 && NotInverted(v) == l1 &&
//         l2 in c2 && Inverted(v) == l2;
//     assert exists c :: c in cnf && NotInverted(v) in c;

//     var f :=  (c: Clause) => NotInverted(v) in c;
//     var where_not_inverted: set<Clause> := set c | c in cnf && f(c);
//     assert exists c :: c in cnf && f(c);
//     SetSetWithSomethingInItIsNotEmpty(cnf, f, where_not_inverted);
//     assume false;
//     assert |where_not_inverted| > 0;


//     // var where_inverted: set<Clause> := set c | c in cnf && Inverted(v) in c;
//     // assert |where_inverted| > 0;

//     // var c1 :| c1 in not_inverted[v];
//     // var c2 :| c2 in inverted[v];

//     cnf
// }

}