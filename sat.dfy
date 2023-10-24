include "util.dfy"

// Provably correct SAT solver
// inspired by https://siddhartha-gadgil.github.io/automating-mathematics/posts/sat-solving/
newtype Variable = int
datatype Literal = 
    True |
    False |
    LitVar(Variable, bool)
{
    function eval(vs: map<Variable,bool>) : (b: bool)
    {
        match this {
            case True => true
            case False => false
            case LitVar(v, inverted) =>
                var val := if v in vs then vs[v] else false;
                if inverted then val else !val
        }
    }

    function full_eval(vs: map<Variable,bool>) : (b: bool)
        requires forall c :: c in vars() ==> c in vs
    {
        match this {
            case True => true
            case False => false
            case LitVar(v, inverted) =>
                var val := vs[v];
                if inverted then val else !val
        }
    }

    function vars() : set<Variable>
    {
        match this {
            case True | False => {}
            case LitVar(v, _) => {v}
        }
    }
}

datatype ClauseLit = Inverted(Variable) | NotInverted(Variable)
{
    function invert() : ClauseLit {
        match this {
            case Inverted(v) => NotInverted(v)
            case NotInverted(v) => Inverted(v)
        }
    }

    function vars() : set<Variable>
    {
        match this {
            case Inverted(v) => {v}
            case NotInverted(v) => {v}
        }
    }

    function eval(vs: map<Variable,bool>) : (b: bool)
    {
        match this {
            case Inverted(v) => if v in vs then !(vs[v]) else true
            case NotInverted(v) => if v in vs then vs[v] else false
        }
    }

    function full_eval(vs: map<Variable,bool>) : (b: bool)
        requires forall c :: c in vars() ==> c in vs
    {
        match this {
            case Inverted(v) => !(vs[v])
            case NotInverted(v) => vs[v]
        }
    }
}

type Clause = set<ClauseLit>
type CNF = set<Clause>

datatype CNFResult = ConstantResult(bool) | VariableResult(CNF)

function clause_vars(clause: Clause) : (vars: set<Variable>)
    ensures forall l :: l in clause ==> vars >= l.vars()
    ensures forall v :: v in vars ==>
        exists l :: l in clause && v in l.vars()
{
    flatten_set(set l | l in clause :: l.vars())
}

lemma MergedClausesHaveSameVars(c1: Clause, c2: Clause)
    ensures clause_vars(c1 + c2) == clause_vars(c1) + clause_vars(c2)
{
    
}

function clause_eval(clause: Clause, vs: map<Variable,bool>) : (b: bool)
{
    exists l :: l in clause && l.eval(vs)
}

ghost function clause_equivalent(c1: Clause, c2: Clause) : (b: bool)
{
    forall vs : map<Variable, bool> :: true ==>
        clause_eval(c1, vs) == clause_eval(c2, vs)
}

function clause_full_eval(clause: Clause, vs: map<Variable,bool>) : (b: bool)
    requires vs.Keys >= clause_vars(clause)
{
    exists l :: l in clause && l.full_eval(vs)
}

function cnf_vars(cnf: CNF) : (vars: set<Variable>)
    ensures forall c :: c in cnf ==> vars >= clause_vars(c)
    ensures forall v :: v in vars ==>
        exists c :: c in cnf && v in clause_vars(c)
{
    flatten_set(set c | c in cnf :: clause_vars(c))
}

function cnf_eval(cnf: CNF, vs: map<Variable,bool>) : (b: bool)
{
    forall c :: c in cnf ==> clause_eval(c, vs)
}

function cnf_full_eval(cnf: CNF, vs: map<Variable,bool>) : (b: bool)
    requires vs.Keys >= cnf_vars(cnf)
{
    forall c :: c in cnf ==> clause_full_eval(c, vs)
}


datatype Expression =
    Constant(bool) |
    Var(Variable, bool) |
    Not(Expression) |
    And(Expression, Expression) |
    Or(Expression,Expression) |
    Implies(Expression, Expression) |
    Equivalent(Expression, Expression)
{
    function children() : (cs: set<Expression>)
    {
        match this {
            case Constant(b) => {}
            case Var(v, _) => {}
            case Not(e) => {e}
            case And(a,b) => {a, b}
            case Or(a,b) => {a, b}
            case Implies(a,b) => {a, b}
            case Equivalent(a,b) => {a, b}
        }
    }
    
    ghost function height() : (h: int)
        ensures h >= 1
    {
        match this {
            case Constant(b) => 1
            case Var(v, _) => 1
            case Not(e) => 1 + e.height()
            case And(a,b) => 1 + max(a.height(), b.height())
            case Or(a,b) => 1 + max(a.height(), b.height())
            case Implies(a,b) => 1 + max(a.height(), b.height())
            case Equivalent(a,b) => 1 + max(a.height(), b.height())
        }
    }

    ghost predicate Valid()
    {
        forall i :: i in children() ==> i.Valid() && i.height() < this.height()
    }

    function self_vars() : (vs: set<Variable>)
    {
        match this {
            case Var(v, _) => {v}
            case _ => {}
        }
    }

    function all_vars() : (vs: set<Variable>)
        requires this.Valid()
        decreases this
        ensures forall v :: true ==> (v in vs <==> v in self_vars() || exists c :: c in children() && v in c.all_vars())
    {
        var vs := flatten_set(match this {
            case Constant(b) => {{}}
            case Var(vv, _) => {{vv}}
            case Not(e) => {e.all_vars()}
            case And(a,b) => {a.all_vars(), b.all_vars()}
            case Or(a,b) => {a.all_vars(), b.all_vars()}
            case Implies(a,b) => {a.all_vars(), b.all_vars()}
            case Equivalent(a,b) => {a.all_vars(), b.all_vars()}
        });

        assert forall v :: true ==> (v in vs <==> v in self_vars() || exists c :: c in children() && v in c.all_vars());

        vs
    }

    function OneEquivalent(a: Expression, b: Expression) : (out: Expression)
        requires a.Valid() && b.Valid()
        ensures out.Valid()
        ensures Equivalent(a,b).equivalent(out)
    {
        ghost var vs: map<Variable, bool> :| true;
        var out := OneEquivalentArbitrary(a, b, vs);

        assert forall m: map<Variable, bool> :: |m.Keys| >= 0 ==> 
            (
                ghost var vs: map<Variable, bool> :| vs == m;
                ghost var out := OneEquivalentArbitrary(a, b, vs);
                assert Equivalent(a,b).eval(vs) == out.eval(vs);
                Equivalent(a,b).eval(m) == out.eval(m)
            );

        out
    }

    function OneEquivalentArbitrary(a: Expression, b: Expression, ghost vs: map<Variable, bool>) : (out: Expression)
        requires a.Valid() && b.Valid()
        ensures out.Valid()
        ensures Equivalent(a,b).eval(vs) == out.eval(vs)
    {
        var eq := Equivalent(a,b);

        var both_true := And(a,b);
        assert both_true.eval(vs) == (a.eval(vs) && b.eval(vs));
        var first_false := Not(a);
        var second_false := Not(b);
        var both_false := And(first_false, second_false);
        assert both_false.eval(vs) == (!a.eval(vs) && !b.eval(vs));
        var out := Or(both_true, both_false);

        assert eq.eval(vs) == out.eval(vs);
        out
    }

    ghost function equivalent(other: Expression) : (eq: bool)
        requires this.Valid()
        requires other.Valid()
    {
        forall vs : map<Variable, bool> :: true ==>
            this.eval(vs) == other.eval(vs)
    }

    ghost function full_equivalent(other: Expression) : (eq: bool)
        requires this.Valid()
        requires other.Valid()
    {
        forall vs : map<Variable, bool> :: vs.Keys >= this.all_vars() + other.all_vars() ==>
            this.full_eval(vs) == other.full_eval(vs)
    }

    ghost function equivalent_cnf(other: CNF) : (eq: bool)
        requires this.Valid()
    {
        forall vs : map<Variable, bool> :: true ==>
            this.eval(vs) == cnf_eval(other, vs)
    }

    ghost function full_equivalent_cnf(cnf: CNF) : (eq: bool)
        requires this.Valid()
    {
        forall vs : map<Variable, bool> :: vs.Keys >= this.all_vars() + cnf_vars(cnf) ==>
            this.full_eval(vs) == cnf_full_eval(cnf, vs)
    }

    lemma also_equivalent_cnf(other: Expression, cnf: CNF)
        requires this.Valid()
        requires other.Valid()
        requires this.equivalent(other)
        requires this.equivalent_cnf(cnf)
        ensures other.equivalent_cnf(cnf)
    {
        assert forall vs : map<Variable, bool> :: true ==>
            this.eval(vs) == other.eval(vs);
        assert forall vs : map<Variable, bool> :: true ==>
            this.eval(vs) == cnf_eval(cnf, vs);
        assert forall vs : map<Variable, bool> :: true ==>
            other.eval(vs) == cnf_eval(cnf, vs);
        assert other.equivalent_cnf(cnf);
    }

    function eval(vs: map<Variable,bool>) : (b: bool)
        requires this.Valid()
        decreases this
    {
        match this {
            case Constant(b) => b
            case Var(v, inverted) =>
                var val := if v in vs then vs[v] else false;
                if inverted then !val else val
            case Not(e) => !e.eval(vs)
            case And(a,b) => a.eval(vs) && b.eval(vs)
            case Or(a,b) => a.eval(vs) || b.eval(vs)
            case Implies(a,b) => !a.eval(vs) || b.eval(vs)
            case Equivalent(a,b) => (a.eval(vs) && b.eval(vs)) || (!a.eval(vs) && !b.eval(vs))
        }
    }

    function full_eval(vs: map<Variable,bool>) : bool
        requires this.Valid()
        requires vs.Keys >= this.all_vars()
        decreases this
    {
        eval(vs)
    }

    predicate no_implies()
        requires Valid()
    {
        match this {
            case Implies(_,_) => false
            case e => forall c :: c in e.children() ==> c.no_implies()
        }
    }

    function remove_implies() : (out: Expression)
        requires Valid()
        decreases this
        ensures out.Valid()
        ensures out.no_implies()
        ensures this.equivalent(out)
    {
        var out := match this {
            case Constant(b) =>
                this
            case Var(v, _) =>
                this
            case Not(x) =>
                var xx := x.remove_implies();
                assert xx.no_implies();
                Not(xx)
            case And(a,b) =>
                And(a.remove_implies(), b.remove_implies())
            case Or(a,b) =>
                Or(a.remove_implies(), b.remove_implies())
            case Implies(a,b) =>
                var a:= a.remove_implies();
                assert a.no_implies() && Not(a).no_implies();
                var b := b.remove_implies();
                assert b.no_implies();
                Or(Not(a), b)
            case Equivalent(a,b) =>
                var a:= a.remove_implies();
                assert a.no_implies();
                var b := b.remove_implies();
                assert b.no_implies();
                Equivalent(a, b)
        };

        assert out.Valid();
        assert out.no_implies();
        assert forall vs: map<Variable,bool> :: vs.Keys >= all_vars() ==> 
            eval(vs) == out.eval(vs);

        out
    }

    predicate no_equivalent() {
        match this {
            case Equivalent(_,_) => false
            case e => forall c :: c in e.children() ==> c.no_equivalent()
        }
    }

    function remove_equivalent() : (out: Expression)
        requires Valid()
        requires no_implies()
        decreases this
        ensures out.Valid()
        ensures out.no_implies()
        ensures out.no_equivalent()
        ensures this.equivalent(out)
    {
        var out := match this {
            case Constant(b) =>
                this
            case Var(v, _) =>
                this
            case Not(x) =>
                var xx := x.remove_equivalent();
                Not(xx)
            case And(a,b) =>
                And(a.remove_equivalent(), b.remove_equivalent())
            case Or(a,b) =>
                Or(a.remove_equivalent(), b.remove_equivalent())
            case Implies(a,b) =>
                assert false;
                a
            case Equivalent(a,b) =>
                OneEquivalent(a.remove_equivalent(), b.remove_equivalent())
        };

        out
    }

    predicate no_not() {
        match this {
            case Not(n) => false
            case e => forall c :: c in e.children() ==> c.no_not()
        }
    }

    predicate no_constant() {
        match this {
            case Constant(_) => false
            case e => forall c :: c in e.children() ==> c.no_constant()
        }
    }

    lemma NotConstantIsInvertedConstant(n: Expression, c: Expression, b: bool)
        requires n == Not(c)
        requires c == Constant(b)
        ensures n.equivalent(Constant(!b))
    {
        assert |map[1 := false].Keys| > 0;
        ghost var m : map<Variable, bool> :| |m.Keys| > 0;
        ghost var not_b := !b;
        assert Not(Constant(b)).eval(m) == Constant(not_b).eval(m);

        assert forall vs : map<Variable, bool> :: |vs.Keys| >= 0 ==>
            ghost var m : map<Variable, bool> :| m == vs;
            ghost var not_b := !b;
            Not(Constant(b)).eval(m) == Constant(not_b).eval(m)
        ;

        assert Not(Constant(b)).equivalent(Constant(!b));
    }

    lemma NotVarIsInvertedVar(n: Expression, ve: Expression, v: Variable, inverted: bool)
        requires n == Not(ve)
        requires ve == Var(v, inverted)
        ensures n.equivalent(Var(v, !inverted))
    {
        assert |map[1 := 1].Keys| >= 0;
        ghost var m : map<Variable, bool> :| |m.Keys| >= 0;
        ghost var not_inverted := !inverted;
        assert Not(Var(v, inverted)).eval(m) == Var(v, not_inverted).eval(m);

        assert forall vs : map<Variable, bool> :: |vs.Keys| >= 0 ==>
            ghost var m : map<Variable, bool> :| m == vs;
            ghost var not_inverted := !inverted;
            Not(Var(v, inverted)).eval(m) == Var(v, not_inverted).eval(m)
        ;

        assert Not(Var(v, inverted)).equivalent(Var(v, not_inverted));
    }

    function replace_not() : (out: Expression)
        requires this.Valid()
        requires this.no_implies()
        requires this.no_equivalent()
        decreases this.height()
        ensures out.Valid()
        ensures out.no_implies()
        ensures out.no_equivalent()
        ensures match out {
            case Constant(_) => true
            case Var(_,_) => true
            case And(_,_) => true
            case Or(_,_) => true
            case Not(_) => false
            case _ => false
        }
        ensures this.equivalent(out)
        ensures out.no_not()
        ensures this.height() >= out.height()
    {
        match this {
            case Not(x) =>
                assert x.height() + 1 == this.height();
                assert x.Valid();
                assert x.no_implies();
                assert x.no_equivalent();
                assert this.equivalent(Not(x));
                var xx := match x {
                    case Constant(b) => 
                        NotConstantIsInvertedConstant(this, x, b);
                        Constant(!b)
                    case Var(v, inverted) => 
                        NotVarIsInvertedVar(this, x, v, inverted);
                        assert this.equivalent(Var(v, !inverted));
                        Var(v, !inverted)
                    case Not(xx) => xx.replace_not()
                    case And(a,b) => 
                        Or(Not(a).replace_not(), Not(b).replace_not())
                    case Or(a,b) =>
                        And(Not(a).replace_not(), Not(b).replace_not())
                    case Implies(a,b) =>
                        assert false;
                        a
                    case Equivalent(a,b) =>
                        assert false;
                        a
                };
                xx
            case Constant(b) => this
            case Var(_, _) => this
            case And(a,b) => And(a.replace_not(), b.replace_not())
            case Or(a,b) => Or(a.replace_not(), b.replace_not())
            case Implies(a,b) => assert false; a
            case Equivalent(a,b) => assert false; a
        }
    }

    function distribute() : (out: CNFResult)
        requires this.Valid()
        requires this.no_implies()
        requires this.no_equivalent()
        requires this.no_not()
        decreases this.height()
        ensures match out {
            case ConstantResult(b) => this.equivalent(Constant(b))
            case VariableResult(cnf) => this.equivalent_cnf(cnf)
        }
    {
        match this {              
            case Constant(b) => ConstantResult(if b then true else false)
            case Var(v, inverted) =>
                VariableResult({{ if inverted then Inverted(v) else NotInverted(v) }})
            case And(a, b) => 
                match (a.distribute(), b.distribute()) {
                    case (ConstantResult(a), ConstantResult(b)) => ConstantResult(a && b)
                    case (ConstantResult(a), VariableResult(b)) => if a then VariableResult(b) else ConstantResult(false)
                    case (VariableResult(a), ConstantResult(b)) => if b then VariableResult(a) else ConstantResult(false)
                    case (VariableResult(a), VariableResult(b)) => VariableResult(a + b)
                }
            case Or(a,b) =>
                var cnf1 := a.distribute();
                var cnf2 := b.distribute();
                match (cnf1, cnf2) {
                    case (ConstantResult(a), ConstantResult(b)) => ConstantResult(a || b)
                    case (ConstantResult(a), VariableResult(b)) => if a then ConstantResult(true) else VariableResult(b)
                    case (VariableResult(a), ConstantResult(b)) => if b then ConstantResult(true) else VariableResult(a)
                    case (VariableResult(cnf1), VariableResult(cnf2)) => VariableResult(MergeCNF(a, b, cnf1, cnf2))
                }
            case Implies(a,b) => assert false; ConstantResult(false)
            case Equivalent(a,b) => assert false; ConstantResult(false)
            case Not(x) => assert false; ConstantResult(false)
        }
    }

    function MergeCNF(a: Expression, b: Expression, cnf1: CNF, cnf2: CNF) : (out: CNF)
        requires this.Valid()
        requires this == Or(a,b)
        requires a.Valid() && a.no_implies() && a.no_equivalent() && a.no_not()
        requires b.Valid() && b.no_implies() && b.no_equivalent() && b.no_not()
        requires a.equivalent_cnf(cnf1)
        requires b.equivalent_cnf(cnf2)
        ensures this.equivalent_cnf(out)
    {
        ghost var vs: map<Variable, bool> :| true;
        var out := this.MergeCNF_Arbitrary(a, b, cnf1, cnf2, vs);
        assert this.eval(vs) == cnf_eval(out, vs);

        assert forall m: map<Variable, bool> :: |m.Keys| >= 0 ==> 
            (
                ghost var vs: map<Variable, bool> :| vs == m;
                ghost var out := this.MergeCNF_Arbitrary(a, b, cnf1, cnf2, vs);
                assert this.eval(vs) == cnf_eval(out, vs);
                this.eval(vs) == cnf_eval(out, vs)
            );
        out
    }

    function MergeCNF_Arbitrary(a: Expression, b: Expression, cnf1: CNF, cnf2: CNF, ghost vs: map<Variable,bool>) : (out: CNF)
        requires this.Valid()
        requires this == Or(a,b)
        requires a.Valid() && a.no_implies() && a.no_equivalent() && a.no_not()
        requires b.Valid() && b.no_implies() && b.no_equivalent() && b.no_not()
        requires a.equivalent_cnf(cnf1)
        requires b.equivalent_cnf(cnf2)
        ensures this.eval(vs) == cnf_eval(out, vs)
    {
        assert this.eval(vs) == cnf_eval(cnf1, vs) || cnf_eval(cnf2, vs);
        assert cnf_eval(cnf1, vs) == forall c1 :: c1 in cnf1 ==> clause_eval(c1, vs);
        assert cnf_eval(cnf2, vs) == forall c2 :: c2 in cnf2 ==> clause_eval(c2, vs);
        assert 
            (cnf_eval(cnf1, vs) || cnf_eval(cnf2, vs))
                ==
            ((forall c1 :: c1 in cnf1 ==> clause_eval(c1, vs)) || (forall c2 :: c2 in cnf2 ==> clause_eval(c2, vs)));
        assert
            ((forall c1 :: c1 in cnf1 ==> clause_eval(c1, vs)) || (forall c2 :: c2 in cnf2 ==> clause_eval(c2, vs)))
                ==
            (forall c1, c2 :: c1 in cnf1 && c2 in cnf2 ==> clause_eval(c1 + c2, vs));
        set c1, c2 | c1 in cnf1 && c2 in cnf2 :: c1 + c2
    }

    function make_cnf() : (out: CNFResult)
        requires Valid()
        ensures match out {
            case VariableResult(out) => this.equivalent_cnf(out)
            case ConstantResult(out) => this.equivalent(Constant(out))
        }
    {
        var out1 := this.remove_implies();
        assert this.equivalent(out1);
        var out2 := out1.remove_equivalent();
        assert out1.equivalent(out2);
        var out3 := out2.replace_not();
        assert out2.equivalent(out3);
        var cnfr := out3.distribute();
        match cnfr {
            case ConstantResult(b) =>
                assert this.equivalent(Constant(b));
                cnfr
            case VariableResult(cnf) =>
                assert out3.equivalent_cnf(cnf);
                out3.also_equivalent_cnf(out2,cnf);
                out2.also_equivalent_cnf(out1,cnf);
                out1.also_equivalent_cnf(this,cnf);
                assert this.equivalent_cnf(cnf);
                cnfr
        }
    }

    function run() : bool
        requires this.Valid()
    {
        var cnf := this.make_cnf();

        false
    }
}





