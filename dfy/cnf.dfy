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


function cnf_remove_tautologies(cnf: CNF) : (out: CNF)
    ensures cnf_equivalent(cnf, out)
{
    set c | c in cnf && !clause_is_tautology(c)
}

}