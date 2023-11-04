include "sat.dfy"

// Clause: l1 ∨ l2 ∨ ... ∨ ln
// CNF: C1 ∧ C2 ∧ ... ∧ Cn

module CNF {
    import opened SAT

function clause_literal_count(c: Clause) : int
{
    |c|
}

function clause_is_tautology(c: Clause) : (out: bool)
    ensures out ==> (
        forall vs: map<Variable,bool> :: true ==> clause_eval(c, vs) == true
    )
{
    exists l1,l2 :: l1 in c && l2 in c && l1.invert() == l2
}


method cnf_literal_count(cnf: CNF) returns (out: int)
{
    out := Util.set_sum(set c | c in cnf :: clause_literal_count(c));
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

function cnf_has_resolution(cnf: CNF) : (out: bool)
{
    exists v, c1, c2 :: v in cnf_vars(cnf) && c1 in cnf && c2 in cnf && cnf_has_resolution_with(cnf, v, c1, c2)
}

function cnf_has_resolution_with(cnf: CNF, v: Variable, c1: Clause, c2: Clause) : (out: bool)
{
    v in cnf_vars(cnf) &&
    c1 in cnf && c2 in cnf && c1 != c2 &&
    NotInverted(v) in c1 &&
    Inverted(v) in c2
}

function merge_resolution_specific(v: Variable, ghost vs: map<Variable, bool>, c1: Clause, c2: Clause) : (out: Clause)
    requires v in vs
    requires NotInverted(v) in c1 && Inverted(v) in c2
    ensures (clause_eval(c1, vs) && clause_eval(c2, vs)) ==> clause_eval(out, vs)
    ensures cnf_implies({c1, c2}, {out})
{
    var c1_others := c1 - {NotInverted(v)};
    var c2_others := c2 - {Inverted(v)};
    c1_others + c2_others
}

function merge_resolution(v: Variable, c1: Clause, c2: Clause) : (out: Clause)
    requires NotInverted(v) in c1 && Inverted(v) in c2
    ensures cnf_implies({c1, c2}, {out})
    ensures forall cnf : CNF :: c1 in cnf && c2 in cnf ==> cnf_implies(cnf, cnf - {c1, c2} + {out})
{
    ghost var example := map[v := true];
    assert v in example;
    ghost var vs :| v in vs;
    merge_resolution_specific(v, vs, c1, c2)
}

method cnf_some_resolution(cnf: CNF) returns (v: Variable, c1: Clause, c2: Clause)
    requires cnf_has_resolution(cnf)
    ensures cnf_has_resolution_with(cnf, v, c1, c2)
{
    v, c1, c2 :| v in cnf_vars(cnf) && c1 in cnf && c2 in cnf && cnf_has_resolution_with(cnf, v, c1, c2);
}

// lemma SetWithSomethingInItIsNotEmpty<T>(s: set<T>, f: T -> bool, ss: set<T>)
//     requires exists x :: x in s && f(x)
//     requires ss == set x | x in s && f(x)
//     ensures |ss| > 0
// {
//     var x :| x in s && f(x);
//     assert x in s;
//     assert f(x);
//     assert x in ss;
//     assert |ss| > 0;
// }

method cnf_resolution_step(cnf: CNF) returns (out: CNF)
    requires !cnf_has_tautologies(cnf)
    requires cnf_has_resolution(cnf)
    ensures cnf_implies(cnf, out)
    ensures |out| < |cnf|
{
    var v,c1,c2 := cnf_some_resolution(cnf);
    assert NotInverted(v) in c1;
    assert c1 != c2;
    var merged := merge_resolution(v, c1, c2);
    assume false;

    assert c1 != merged;
    assert c2 != merged;
    out := cnf - {c1, c2} + {merged};
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