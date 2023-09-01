include "util.dfy"

// Provably correct SAT solver
// inspired by https://siddhartha-gadgil.github.io/automating-mathematics/posts/sat-solving/
newtype Variable = int

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
        ensures h >= 0
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
        var vs := flatten(match this {
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

        assert forall m: map<Variable, bool> :: true ==> 
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

    function eval(vs: map<Variable,bool>) : bool
        requires this.Valid()
        decreases this
    {
        match this {
            case Constant(b) => b
            case Var(v, inverted) =>
                var val := if v in vs then vs[v] else false;
                if inverted then val else !val
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

    lemma NotConstantIsInvertedConstant(n: Expression, c: Expression, b: bool)
        requires n == Not(c)
        requires c == Constant(b)
        ensures n.equivalent(Constant(!b))
    {
        ghost var m : map<Variable, bool> :| true;
        assert Not(Constant(b)).eval(m) == Constant(!b).eval(m);

        assert forall vs : map<Variable, bool> {:trigger true} :: true ==>
            ghost var m : map<Variable, bool> :| m == vs;
            Not(Constant(b)).eval(m) == Constant(!b).eval(m)
        ;

        assert Not(Constant(b)).equivalent(Constant(!b));
    }

    lemma NotVarIsInvertedVar(n: Expression, ve: Expression, v: Variable, inverted: bool)
        requires n == Not(ve)
        requires ve == Var(v, inverted)
        ensures n.equivalent(Var(v, !inverted))
    {
        ghost var m : map<Variable, bool> :| true;
        assert Not(Var(v, inverted)).eval(m) == Var(v, !inverted).eval(m);

        assert forall vs : map<Variable, bool> {:trigger true} :: true ==>
            ghost var m : map<Variable, bool> :| m == vs;
            Not(Var(v, inverted)).eval(m) == Var(v, !inverted).eval(m)
        ;

        assert Not(Var(v, inverted)).equivalent(Var(v, !inverted));
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




    function simplify() : (out: Expression)
        requires Valid()
        ensures out.Valid()
        ensures out.no_implies()
        ensures out.no_equivalent()
        ensures out.no_not()
        ensures this.equivalent(out)
    {
        var out := this;
        var out := out.remove_implies();
        var out := out.remove_equivalent();
        var out := out.replace_not();
        out
    }
}





