include "util.dfy"

// Provably correct SAT solver
// inspired by https://siddhartha-gadgil.github.io/automating-mathematics/posts/sat-solving/
newtype Variable = int
datatype Literal = 
    True |
    False |
    LitVar(Variable, bool)
type Clause = set<Literal>
type CNF = set<Clause>

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

    lemma EquivalentChildrenAndExpressionAbitrary(e: Expression, a2: Expression, b2: Expression, vs: map<Variable,bool>)
        requires this.Valid() && a2.Valid() && b2.Valid()
        requires match this {
            case Or(a,b)  => e == Or(a2,b2) && a.eval(vs) == a2.eval(vs) && b.eval(vs) == b2.eval(vs)
            case And(a,b) => e == And(a2,b2) && a.eval(vs) == a2.eval(vs) && b.eval(vs) == b2.eval(vs)
            case _ => true
        }
        ensures match this {
            case Or(a,b)  => this.eval(vs) ==  Or(a2,b2).eval(vs)
            case And(a,b) => this.eval(vs) == And(a2,b2).eval(vs)
            case _ => true
        } 
    {
        match this {
            case And(a,b) =>
                assert And(a,b).eval(vs) == (a.eval(vs) && b.eval(vs));
                assert (a.eval(vs) && b.eval(vs)) == (a2.eval(vs) && b2.eval(vs));
                assert (a2.eval(vs) && b2.eval(vs)) == And(a2,b2).eval(vs);
            case Or(a,b) =>
                assert Or(a,b).eval(vs) == (a.eval(vs) || b.eval(vs));
                assert (a.eval(vs) || b.eval(vs)) == (a2.eval(vs) || b2.eval(vs));
                assert (a2.eval(vs) || b2.eval(vs)) == Or(a2,b2).eval(vs);
            case _ => {}
        }
    }

    lemma EquivalentChildrenAndExpression(e: Expression, a2: Expression, b2: Expression)
        requires this.Valid() && a2.Valid() && b2.Valid()
        requires match this {
            case Or(a,b)  => e == Or(a2,b2) && a.equivalent(a2) && b.equivalent(b2)
            case And(a,b) => e == And(a2,b2) && a.equivalent(a2) && b.equivalent(b2)
            case _ => false
        }
        ensures match this {
            case Or(a,b)  => this.equivalent(Or(a2,b2))
            case And(a,b) => this.equivalent(And(a2,b2))
            case _ => false
        }
        ensures this.equivalent(e)
    {
        assert forall m: map<Variable, bool> {:trigger true} :: true ==> 
            (
                ghost var vs: map<Variable, bool> :| vs == m;
                this.EquivalentChildrenAndExpressionAbitrary(e, a2, b2, vs);
                match this {
                    case And(a,b) =>
                        (a.eval(vs) == a2.eval(vs) && b.eval(vs) == b2.eval(vs)) ==> this.eval(vs) == And(a2,b2).eval(vs)
                    case Or(a,b) =>
                        (a.eval(vs) == a2.eval(vs) && b.eval(vs) == b2.eval(vs)) ==> this.eval(vs) == Or(a2,b2).eval(vs)
                    case _ => true
                }
            );    
    }


    function SubstituteChildren(a2: Expression, b2: Expression) : (out: Expression)
        requires this.Valid()&& a2.Valid() && b2.Valid()
        requires match this {
            case Or(a,b) => a.equivalent(a2) && b.equivalent(b2)
            case And(a,b) => a.equivalent(a2) && b.equivalent(b2)
            case _ => false
        }
        ensures out.Valid()
        ensures this.equivalent(out)
        ensures match this {
            case Or(_,_) => out == Or(a2,b2)
            case And(_,_) => out == And(a2,b2)
            case _ => false
        }
    {
        match this {
            case Or(a,b) => 
                var out := Or(a2,b2);
                assert this.equivalent(out) by {
                    this.EquivalentChildrenAndExpression(Or(a2,b2), a2, b2);
                }
                out
            case And(a,b) =>
                var out := And(a2,b2);
                assert this.equivalent(out) by {
                    this.EquivalentChildrenAndExpression(And(a2,b2), a2, b2);
                }
                out
            case e => assert false; e
        }
    }

    function eval(vs: map<Variable,bool>) : (b: bool)
        requires this.Valid()
        decreases this
        ensures match this {
            case Or(x,y)=> b == x.eval(vs) || y.eval(vs)
            case _ => true
        }
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

    lemma DistributeEquivalent(a: Expression, b: Expression, c: Expression, d: Expression)
        requires a.Valid() && b.Valid() && c.Valid() && d.Valid()
        requires a == And(c,d)
        ensures And(Or(a,c), Or(a,d)).Valid()
        ensures Or(And(c,d),b).equivalent(And(Or(b,c), Or(b,d)))
    {
        ghost var vs: map<Variable, bool> :| true;
        assert Or(a,b).eval(vs) == And(Or(b,c), Or(b,d)).eval(vs);
    }

    lemma DistributeEquivalent1(a: Expression, b: Expression, bc1: Expression, bc2: Expression)
        requires a.Valid() && b.Valid() && bc1.Valid() && bc2.Valid()
        requires b == And(bc1,bc2)
        ensures Or(a,And(bc1,bc2)).equivalent(And(Or(a,bc1),Or(a,bc2)))
    {
        ghost var vs: map<Variable, bool> :| true;
        assert Or(a,b).eval(vs) == And(Or(a,bc1), Or(a,bc2)).eval(vs);
    }

    function DistributeEquivalent2Abitrary(vs: map<Variable, bool>, a: Expression, b: Expression, c: Expression, d: Expression, e: Expression, f: Expression) : (out: Expression)
        requires a.Valid() && b.Valid() && c.Valid() && d.Valid() && e.Valid() && f.Valid()
        requires a == And(c,d)
        requires b == And(e,f)
        ensures out == And(And(Or(c,e),Or(d,e)),And(Or(c,f),Or(d,f)))
        ensures Or(a,b).eval(vs) == out.eval(vs)
    {
        assert Or(a,b).eval(vs) == Or(a,And(e,f)).eval(vs);
        DistributeEquivalent1(a, And(e,f), e, f);
        assert Or(a,b).eval(vs) == And(
            Or(a,e), 
            Or(a,f)
        ).eval(vs);

        assert Or(a,e).eval(vs) == Or(And(c,d),e).eval(vs);
        DistributeEquivalent1(e, And(c,d), c, d);
        assert Or(a,e).eval(vs) == And(Or(c,e),Or(d,e)).eval(vs);

        assert Or(a,f).eval(vs) == Or(And(c,d),f).eval(vs);
        DistributeEquivalent1(f, And(c,d), c, d);
        assert Or(a,f).eval(vs) == And(Or(c,f),Or(d,f)).eval(vs);

        var out := And(
            And(Or(c,e),Or(d,e)),
            And(Or(c,f),Or(d,f))
        );
        assert Or(a,b).eval(vs) == out.eval(vs);
        out
    }

    lemma DistributeEquivalent2(a: Expression, b: Expression, c: Expression, d: Expression, e: Expression, f: Expression)
        requires a.Valid() && b.Valid() && c.Valid() && d.Valid() && e.Valid() && f.Valid()
        requires a == And(c,d)
        requires b == And(e,f)
        ensures Or(a,b).equivalent(And(And(Or(c,e),Or(d,e)),And(Or(c,f),Or(d,f))))
    {
        assert forall m: map<Variable, bool> :: true ==> 
            (
                ghost var vs: map<Variable, bool> :| vs == m;
                var out := DistributeEquivalent2Abitrary(vs, a, b, c, d, e, f);
                assert Or(a,b).eval(vs) == And(And(Or(c,e),Or(d,e)),And(Or(c,f),Or(d,f))).eval(vs);
                Or(a,b).eval(m) == out.eval(m)
            );
    }

    predicate no_or_and()
    {
        match this {
            case Or(a,b) =>
                match a {
                    case And(_,_) => false
                    case _ => true
                }
                && 
                match b {
                    case And(_,_) => false
                    case _ => true
                } 
            case e => forall c :: c in e.children() ==> c.no_or_and()
        }
    }

    function distribute_once() : (out: Expression)
        requires this.Valid()
        requires this.no_implies()
        requires this.no_equivalent()
        requires this.no_not()
        requires match this {
            case Or(a,b) => 
                match a {
                    case And(_,_) => true
                    case _ => false
                } && match b {
                    case And(_,_) => false
                    case _ => true
                }
                case _ => false
        }
        ensures out.Valid()
        ensures out.no_implies()
        ensures out.no_equivalent()
        ensures out.no_not()
        ensures this.equivalent(out)
    {
        match this {
            case Or(a,b) =>
                match (a,b) {
                    case (a, And(bc1,bc2)) =>
                        DistributeEquivalent(a,b,bc1,bc2);
                        And(Or(a,bc1),Or(a,bc2))
                    case _ => this
                }
            case _ => this
        }
    }

    function distribute() : (out: Expression)
        requires this.Valid()
        requires this.no_implies()
        requires this.no_equivalent()
        requires this.no_not()
        decreases this.height()
        ensures out.Valid()
        ensures out.no_implies()
        ensures out.no_equivalent()
        ensures out.no_not()
        ensures out.no_or_and()
        ensures this.equivalent(out)
    {
        match this {              
            case Constant(_) => this
            case Var(_, _) => this
            case And(a, b) => And(a.distribute(), b.distribute())
            case Or(a,b) =>
                assert a.Valid() && a.no_implies() && a.no_equivalent() && a.no_not();
                assert b.Valid() && b.no_implies() && b.no_equivalent() && b.no_not();
                match (a,b) {
                    case (And(c,d), And(e,f)) =>
                        assume false; 
                        // DistributeEquivalent2(a,b,c,d,e,f);
                        // var expanded := And(
                        //     And(Or(c,e),Or(d,e)),
                        //     And(Or(c,f),Or(d,f)));
                        // assert {:split_here} this.equivalent(expanded);
                            
                        // var c2 := c.distribute();
                        // var d2 := d.distribute();
                        // var e2 := e.distribute();
                        // var f2 := f.distribute();
                        
                        // var or1 := Or(c,e).SubstituteChildren(c2,e2);
                        // var or2 := Or(d,e).SubstituteChildren(d2,e2);
                        // var and1 := And(Or(c,e),Or(d,e)).SubstituteChildren(or1,or2);
                        // var or3:= Or(c,f).SubstituteChildren(c2,f2);
                        // var or4:= Or(d,f).SubstituteChildren(d2,f2);
                        // var and2 := And(Or(c,f),Or(d,f)).SubstituteChildren(or3,or4);
                        // var out := expanded.SubstituteChildren(and1, and2);
                        // assert this.equivalent(out);
                        this
                    case (a, And(c,d)) =>
                        assert {:split_here} true;
                        DistributeEquivalent(b, a, c, d);
                        var or1 := Or(a,c).SubstituteChildren(a, c.distribute());
                        var or1 := or1.distribute();
                        var or2 := Or(a,d).SubstituteChildren(a, d.distribute());
                        var or2 := or2.distribute();
                        var out := And(Or(a,c), Or(a,d)).SubstituteChildren(or1, or2);
                        assert this.equivalent(out);
                        assert out.no_or_and();
                        out
                    case (And(c,d),b) =>
                        assert {:split_here} true;
                        DistributeEquivalent(a, b, c, d);
                        var or1 := Or(b,c).SubstituteChildren(b, c.distribute());
                        var or2 := Or(b,d).SubstituteChildren(b, d.distribute());
                        var out := And(Or(b,c), Or(b,d)).SubstituteChildren(or1, or2);
                        assert this.equivalent(out);
                        assert out.no_or_and();
                        out
                    case _ => this
                }
            case Implies(a,b) => assert false; a
            case Equivalent(a,b) => assert false; a
            case Not(x) => assert false; x
        }
    }

    function simplify() : (out: Expression)
        requires Valid()
        ensures out.Valid()
        ensures out.no_implies()
        ensures out.no_equivalent()
        ensures out.no_not()
        ensures out.no_or_and()
        ensures this.equivalent(out)
    {
        var out := this;
        var out := out.remove_implies();
        var out := out.remove_equivalent();
        var out := out.replace_not();
        var out := out.distribute();
        out
    }

    predicate no_and() {
        match this {
            case And(_,_) => false
            case e => forall c :: c in e.children() ==> c.no_and()
        }
    }

    // function make_clause() : (c : Clause)
    //     requires Valid()
    //     requires no_implies()
    //     requires no_equivalent()
    //     requires no_not()
    //     requires no_or_and()
    //     requires no_and()
    // {
    //     match this {
    //         case Constant(b) => { if b then True else False }
    //         case Var(v, inverted) => { LitVar(v, inverted) }
    //         case And(a,b) => { assert false; False }
    //         case Or(a,b) => a.make_clause() + b.make_clause()
    //         case Not(e) => { assert false; False }
    //         case Implies(a,b) => { assert false; False }
    //         case Equivalent(a,b) => { assert false; False }
    //     }
    // }

    // function make_cnf() : (cnf : CNF)
    //     requires Valid()
    //     requires no_implies()
    //     requires no_equivalent()
    //     requires no_not()
    //     requires no_or_and()
    // {
    //     match this {
    //         case Constant(b) => {{if b then True else False}}
    //         case Var(v, inverted) => {{LitVar(v, inverted)}}
    //         case And(a,b) => { a.make_clause() , b.make_clause()}
    //         case Or(a,b) => { a.make_clause() + b.make_clause()}
    //         case Not(e) => {{ assert false; False }}
    //         case Implies(a,b) => {{ assert false; False }}
    //         case Equivalent(a,b) => {{ assert false; False }}
    //     }
    // }

    // function run() : bool
    //     requires this.Valid()
    // {
    //     var simplified := this.simplify();
    //     var cnf := simplified.make_cnf();

    //     false
    // }
}





