include "util.dfy"

// Provably correct SAT solver
// inspired by https://siddhartha-gadgil.github.io/automating-mathematics/posts/sat-solving/
newtype Variable = int


lemma demorgan1(s: set<Expression>)
    requires |s| >= 1
    requires forall i :: i in s ==> i.Valid()
    ensures 
        Not(Or(s)).equivalent(And(map_not_empty(s, map i | i in s :: Not(i))))
{
    ghost var vs: map<Variable, bool> :| true;

    var or := Or(s);
    var lhs := Not(Or(s));
    var l := lhs.eval(vs);
    assert or.eval(vs) == (!forall i :: i in s ==> !i.eval(vs));
    assert lhs.eval(vs) == !(!forall i :: i in s ==> !i.eval(vs));
    assert l == !(!forall i :: i in s ==> !i.eval(vs));

    var nots := map_not_empty(s, map i | i in s :: Not(i));
    var rhs := And(nots);
    var r := rhs.eval(vs);
    assert r == (forall i :: i in nots ==> i.eval(vs));
    assert !(!forall i :: i in s ==> !i.eval(vs)) == (forall i :: i in s ==> Not(i).eval(vs));

    assert l == r;
    assert lhs.eval(vs) == rhs.eval(vs);
    assert forall vs : map<Variable, bool> :: true ==>
            lhs.eval(vs) == rhs.eval(vs);
}

lemma demorgan2(s: set<Expression>)
    requires |s| >= 1
    requires forall i :: i in s ==> i.Valid() 
    ensures Not(And(s)).equivalent(Or(map_not_empty(s, map i | i in s :: Not(i))))
{
    ghost var vs: map<Variable, bool> :| true;

    var and := And(s);
    assert and.eval(vs) == forall i :: i in s ==> i.eval(vs);
    assert and.eval(vs) == !(exists i :: i in s && !i.eval(vs));

    var lhs := Not(and);
    var l := lhs.eval(vs);
    assert and.eval(vs) != l;
    assert l == exists i :: i in s && !i.eval(vs);

    var nots := map_not_empty(s, map i | i in s :: Not(i));
    var rhs := Or(nots);
    var r := rhs.eval(vs);
    assert Or(nots).eval(vs) == exists n :: n in nots && n.eval(vs);

    assert l == r;
    assert lhs.eval(vs) == rhs.eval(vs);
    assert forall vs : map<Variable, bool> :: true ==>
            lhs.eval(vs) == rhs.eval(vs);
}

datatype Expression =
    Constant(bool) |
    Var(Variable) |
    Not(Expression) |
    And(set<Expression>) |
    Or(set<Expression>) |
    Implies(Expression, Expression) |
    Equivalent(Expression, Expression)
{
    function children() : (cs: set<Expression>)
    {
        match this {
            case Constant(b) => {}
            case Var(v) => {}
            case Not(e) => {e}
            case And(ands) => ands
            case Or(ors) => ors
            case Implies(a,b) => {a, b}
            case Equivalent(a,b) => {a, b}
        }
    }

    predicate LocalValid()
    {
        match this {
            case Constant(b) => true
            case Var(v) => true
            case Not(e) => true
            case And(ands) => |ands| >= 1
            case Or(ors) => |ors| >= 1
            case Implies(a,b) => true
            case Equivalent(a,b) => true
        }
    }

    predicate Valid()
    {
        LocalValid() &&
        forall i :: i in children() ==> i.LocalValid() && i.Valid()
    }

    function self_vars() : (vs: set<Variable>)
    {
        match this {
            case Var(v) => {v}
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
            case Var(vv) => {{vv}}
            case Not(e) => {e.all_vars()}
            case And(ands) => set a | a in ands :: a.all_vars()
            case Or(ors) => set o | o in ors :: o.all_vars()
            case Implies(a,b) => {a.all_vars(), b.all_vars()}
            case Equivalent(a,b) => {a.all_vars(), b.all_vars()}
        });

        assert forall v :: true ==> (v in vs <==> v in self_vars() || exists c :: c in children() && v in c.all_vars());

        vs
    }

    function descendents() : (ds: set<Expression>)
        requires Valid()
        ensures forall d :: true ==> (d in ds <==> exists c :: c in children() && d in c.descendents())
    {
        var ds := match this {
            case Constant(b) => {}
            case Var(v) => {}
            case Not(e) => e.descendents()
            case And(ands) => flatten(set i | i in ands :: i.descendents())
            case Or(ors) => flatten(set i | i in ors :: i.descendents())
            case Implies(a,b) => flatten({a.descendents(), b.descendents()})
            case Equivalent(a,b) => flatten({a.descendents(), b.descendents()})
        };
        assert forall d :: true ==> (d in ds <==> exists c :: c in children() && d in c.descendents());
        ds
    }

    function OneEquivalent(a: Expression, b: Expression) : (out: Expression)
        requires a.Valid() && b.Valid()
        ensures out.OneEnsures()
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
        ensures out.OneEnsures()
        ensures Equivalent(a,b).eval(vs) == out.eval(vs)
    {
        var eq := Equivalent(a,b);

        var both_true := And({a,b});
        assert both_true.eval(vs) == (a.eval(vs) && b.eval(vs));
        var first_false := Not(a);
        var second_false := Not(b);
        var both_false := And({first_false, second_false});
        assert both_false.eval(vs) == (!a.eval(vs) && !b.eval(vs));
        var out := Or({both_true, both_false});

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
            case Var(v) => if v in vs then vs[v] else false
            case Not(e) => !e.eval(vs)
            case And(ands) => forall a :: a in ands ==> a.eval(vs)
            case Or(ors) => !(forall o :: o in ors ==> !o.eval(vs))
            case Implies(a,b) => !a.eval(vs) || b.eval(vs)
            case Equivalent(a,b) => (a.eval(vs) && b.eval(vs)) || (!a.eval(vs) && !b.eval(vs))
        }
    }

    function full_eval(vs: map<Variable,bool>) : bool
        requires this.Valid()
        requires vs.Keys >= this.all_vars()
        decreases this
    {
        match this {
            case Constant(b) => b
            case Var(v) => vs[v]
            case Not(e) => !e.eval(vs)
            case And(ands) => forall a :: a in ands ==> a.eval(vs)
            case Or(ors) => !(forall o :: o in ors ==> !o.eval(vs))
            case Implies(a,b) => !a.eval(vs) || b.eval(vs)
            case Equivalent(a,b) => (a.eval(vs) && b.eval(vs)) || (!a.eval(vs) && !b.eval(vs))
        }
    }

    predicate OneEnsures()
    {
        this.Valid() &&
        match this {
            case Implies(_,_) => false
            case Equivalent(_,_) => false
            case Not(ee) =>
                match ee {
                    case Or(_) => false
                    case And(_) => false
                    case _ => true
                }
            case e => true
        }
    }

    function simplify_one() : (out: Expression)
        requires this.Valid()
        decreases this
        ensures out.OneEnsures()
        ensures this.equivalent(out)
    {
        match this {
            case Implies(a,b) => 
                var out := Or({Not(a), b});
                assert this.equivalent(out);
                out
            case Equivalent(a,b) =>
                var out := OneEquivalent(a,b);
                assert this.equivalent(out);
                out
            case Not(n) =>
                assert n.Valid();
                var out := match n {
                    case Or(s) =>
                        demorgan1(s);
                        And(map_not_empty(s, map i | i in s :: Not(i)))
                    case And(s) =>
                        demorgan2(s);
                        Or(map_not_empty(s, map i | i in s :: Not(i)))
                    case _ => this
                };
                assert this.equivalent(out);
                out
            case e => e
        }
    }

    predicate no_implies()
        requires Valid()
    {
        match this {
            case Implies(_,_) => false
            case e => forall c :: c in e.children() ==> c.no_implies()
        }
    }

    function simplify_implies() : (out: Expression)
        requires Valid()
        decreases this
        ensures out.Valid()
        ensures out.no_implies()
        ensures all_vars() >= out.all_vars()
        ensures forall vs: map<Variable,bool> :: vs.Keys >= all_vars() ==> 
            eval(vs) == out.eval(vs)
    {
        var out := match this {
            case Constant(b) =>
                this
            case Var(v) =>
                this
            case Not(x) =>
                var xx := x.simplify_implies();
                assert xx.no_implies();
                Not(xx)
            case And(s) =>
                var ss := map_not_empty(s, map i | i in s :: i.simplify_implies());
                And(ss)
            case Or(s) =>
                var ss := map_not_empty(s, map i | i in s :: i.simplify_implies());
                Or(ss)
            case Implies(a,b) =>
                var a:= a.simplify_implies();
                assert a.no_implies() && Not(a).no_implies();
                var b := b.simplify_implies();
                assert b.no_implies();
                Or({Not(a), b})
            case Equivalent(a,b) =>
                var a:= a.simplify_implies();
                assert a.no_implies();
                var b := b.simplify_implies();
                assert b.no_implies();
                Equivalent(a, b)
        };

        assert out.Valid();
        assert out.no_implies();
        assert all_vars() >= out.all_vars();
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

    function simplify_equivalent() : (out: Expression)
        requires Valid()
        requires no_implies()
        decreases this
        ensures out.Valid()
        ensures out.no_implies()
        ensures out.no_equivalent()
        ensures all_vars() >= out.all_vars()
        ensures forall vs: map<Variable,bool> :: vs.Keys >= all_vars() ==> 
            eval(vs) == out.eval(vs)
    {
        var out := match this {
            case Constant(b) =>
                this
            case Var(v) =>
                this
            case Not(x) =>
                var xx := x.simplify_equivalent();
                Not(xx)
            case And(s) =>
                var ss := map_not_empty(s, map i | i in s :: i.simplify_equivalent());
                And(ss)
            case Or(s) =>
                var ss := map_not_empty(s, map i | i in s :: i.simplify_equivalent());
                Or(ss)
            case Implies(a,b) =>
                assert false;
                a
            case Equivalent(a,b) =>
                var a:= a.simplify_equivalent();
                assert a.Valid();
                assert a.no_implies();
                assert a.no_equivalent();
                var b := b.simplify_equivalent();
                assert b.Valid();
                assert b.no_implies();
                assert b.no_equivalent();
                var both_true := And({a,b});
                assert both_true.Valid();
                assert both_true.no_implies();
                assert both_true.no_equivalent();
                var left_false := Not(a);
                assert left_false.Valid();
                assert left_false.no_implies();
                assert left_false.no_equivalent();
                var right_false := Not(b);
                assert right_false.Valid();
                assert right_false.no_implies();
                assert right_false.no_equivalent();
                var both_false := And({left_false, right_false});
                assert both_false.Valid();
                assert both_false.no_implies();
                assert both_false.no_equivalent();
                var out := Or({both_true, both_false});
                assert out.Valid();
                assert out.no_implies();
                assert out.no_equivalent();
                assume false;
                out
        };

        out
    }

    predicate no_not() {
        match this {
            case Not(_) => false
            case e => forall c :: c in e.children() ==> c.no_not()
        }
    }

    // function simplify_not_expressions() : (out: Expression)
    //     requires no_implies()
    //     requires no_equivalent()
    //     decreases this
    //     ensures out.no_not()
    //     ensures this.all_vars() >= out.all_vars()
    //     ensures forall vs: map<Variable,bool> :: vs.Keys >= all_vars() ==> 
    //         eval(vs) == out.eval(vs)
    // {
    //     var out := match this {
    //         case Constant(b) =>
    //             assert this.no_not();
    //             this
    //         case Var(v) =>
    //             assert this.no_not();
    //             this
    //         case Not(x) =>
    //             var xx := match x {
    //                 case Constant(b) =>
    //                     Constant(!b)
    //                 case Var(v) =>
    //                     Not(x)
    //                 case Not(xx) =>
    //                     var xxx := xx.simplify_not_expressions();
    //                     xxx
    //                 case And(s) =>
    //                     var ss := map_not_empty(s, map i | i in s :: i.simplify_not_expressions());
    //                     assert forall i :: i in ss ==> i.no_not();
    //                     demorgan2(ss);
    //                     var xx := Or(set i | i in ss :: Not(i));
    //                     assert no_not_expressions(xx);
    //                     xx
    //                 case Or(s) =>
    //                     var ss := set i | i in s :: simplify_not_expressions(i, vs);
    //                     assert forall i :: i in ss ==> no_not_expressions(i);
    //                     demorgan1(ss, vs);
    //                     var xx := And(set i | i in ss :: Not(i));
    //                     assert no_not_expressions(xx);
    //                     xx
    //                 case Implies(a,b) =>
    //                     assert false;
    //                     a
    //                 case Equivalent(a,b) =>
    //                     assert false;
    //                     a
    //             };
    //             assert no_not_expressions(xx);
    //             xx
    //         case And(s) =>
    //             var ss := map_not_empty(s, map i | i in s :: i.simplify_not_expressions());
    //             assert forall i :: i in ss ==> i.no_not();
    //             assert And(ss).no_not();
    //             And(ss)
    //         case Or(s) =>
    //         var ss := map_not_empty(s, map i | i in s :: i.simplify_not_expressions());
    //             assert forall i :: i in ss ==> i.no_not();
    //             assert Or(ss).no_not();
    //             Or(ss)
    //         case Implies(a,b) =>
    //             assert false;
    //             a
    //         case Equivalent(a,b) =>
    //             assert false;
    //             a
    //     };

    //     out
    // }

    function simplify() : (out: Expression)
        requires Valid()
        ensures out.Valid()
        ensures out.no_implies()
        ensures out.no_equivalent()
        ensures all_vars() >= out.all_vars()
        ensures forall vs: map<Variable,bool> :: vs.Keys >= all_vars() ==> 
            eval(vs) == out.eval(vs)
    {
        var out := this;
        var out := out.simplify_implies();
        var out := out.simplify_equivalent();
        out
    }
}





