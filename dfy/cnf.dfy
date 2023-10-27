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
    if |c| == 1 then
        Util.extract_only_from_set(c)
    else
        var lambda := (l: ClauseLit) => l.number();
        SAT.NumbersBijection(c, lambda);
        Util.extract_max_from_set(c, lambda)
}

// function clause_gt(c1: Clause, c2: Clause) : (out: bool)
//     requires c1 != c2
// {
//     if |c1| > |c2| then
//         true
//     else if |c1| < |c2| then
//         false
//     else
//         assert |c1| == |c2|;

// }

// function max_clause(cs: set<Clause>) : (out: Clause)
//     requires |cs| > 0
// {
//     var c :| c in cs && forall cc :: cc in cs && cc != c ==>  c >= cc;
//     c
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

// function cnf_has_resolution(cnf: CNF) : (out: bool)
//     ensures out == (exists v :: v in cnf_vars(cnf) && cnf_has_resolution_with_var(cnf, v))
// {
//     exists v :: v in cnf_vars(cnf) && cnf_has_resolution_with_var(cnf, v)
// }

// function cnf_has_resolution_with_var(cnf: CNF, v: Variable) : (out: bool)
//     ensures out == (exists l1, l2, c1, c2 ::
//         v in cnf_vars(cnf) &&
//         c1 in cnf && c2 in cnf && c1 != c2 &&
//         l1 in c1 && NotInverted(v) == l1 &&
//         l2 in c2 && Inverted(v) == l2)
// {
//     exists l1, l2, c1, c2 ::
//         v in cnf_vars(cnf) &&
//         c1 in cnf && c2 in cnf && c1 != c2 &&
//         l1 in c1 && NotInverted(v) == l1 &&
//         l2 in c2 && Inverted(v) == l2
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

//     var where_not_inverted: set<Clause> := set c | c in cnf && NotInverted(v) in c;
//     assert |where_not_inverted| > 0;
//     // var where_inverted: set<Clause> := set c | c in cnf && Inverted(v) in c;
//     // assert |where_inverted| > 0;

//     // var c1 :| c1 in not_inverted[v];
//     // var c2 :| c2 in inverted[v];

//     cnf
// }

}