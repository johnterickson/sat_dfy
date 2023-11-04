import "SAT.dfy"

// Clause: l1 ∨ l2 ∨ ... ∨ ln
// CNF: C1 ∧ C2 ∧ ... ∧ Cn

module CNF {
    import opened SAT

function clause_literal_count(c: Clause) : (out: int)
    ensures out >= 0
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


function cnf_literal_count(cnf: CNF) : (out: int)
    ensures out >= 0
{
    var cnts := map c | c in cnf :: clause_literal_count(c);
    Util.map_sum(cnts)
    // Util.NonNegativesSumToNonNegative(cnts);
    // Util.set_sum(cnts)
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
    ensures clause_literal_count(out) < clause_literal_count(c1) + clause_literal_count(c2)
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

method cnf_resolution_step(cnf: CNF) returns (out: CNF)
    requires !cnf_has_tautologies(cnf)
    requires cnf_has_resolution(cnf)
    ensures !cnf_has_tautologies(out)
    ensures cnf_implies(cnf, out)
    ensures cnf_literal_count(out) < cnf_literal_count(cnf)
{
    var v,c1,c2 := cnf_some_resolution(cnf);
    assert NotInverted(v) in c1;
    assert c1 != c2;
    var merged := merge_resolution(v, c1, c2);

    out := cnf - {c1, c2} + {merged};
    assert cnf_implies(cnf, out);
    assert clause_literal_count(merged) < clause_literal_count(c1) + clause_literal_count(c2);
    assume false;

    assert cnf_literal_count(out) == cnf_literal_count(cnf) - clause_literal_count(c1) - clause_literal_count(c2) + clause_literal_count(merged);
}

// method cnf_resolution(cnf: CNF) returns (out: CNF)
//     requires !cnf_has_tautologies(cnf)
//     ensures !cnf_has_resolution(cnf)
//     ensures cnf_implies(cnf, out)
// {
//     out := cnf;

//     while cnf_has_resolution(out)
//         invariant !cnf_has_tautologies(out)
//         invariant cnf_implies(cnf, out)
//         decreases cnf_literal_count(out)
//     {
//         var out' := cnf_resolution_step(out);
//         assert cnf_implies(cnf, out);
//         assert cnf_implies(out, out');
//         assert cnf_implies(cnf, out');
//         assert cnf_literal_count(out') < cnf_literal_count(out);
//     }
// }

}