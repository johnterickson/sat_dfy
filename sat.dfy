include "util.dfy"

// Provably correct SAT solver
// inspired by https://siddhartha-gadgil.github.io/automating-mathematics/posts/sat-solving/
newtype Variable = int

datatype Expression = 
    Constant(bool) |
    Var(Variable) |
    Not(Expression) |
    And(set<Expression>) |
    Or(set<Expression>) |
    Implies(Expression, Expression) | 
    Equivalent(Expression, Expression)

function children(e: Expression) : (cs: set<Expression>)
    decreases e
    ensures e !in cs
{
    match e {
        case Constant(b) => {}
        case Var(v) => {}
        case Not(e) => {e}
        case And(ands) => ands
        case Or(ors) => ors
        case Implies(a,b) => {a, b}
        case Equivalent(a,b) => {a, b}
    }
}

function descendents(e: Expression) : (d: set<Expression>)
    decreases e
    ensures e !in d
    ensures children(e) <= d
    ensures forall i :: i in d ==> height(e) > height(i)
    ensures forall i :: i in children(e) ==> descendents(i) < d
{
    match e {
        case Constant(b) => {}
        case Var(v) => {}
        case Not(x) => {x} + descendents(x)
        case And(s) => s + flatten(set i | i in s :: descendents(i))
        case Or(s) => s + flatten(set i | i in s :: descendents(i))
        case Implies(a,b) => {a, b} + descendents(a) + descendents(b)
        case Equivalent(a,b) => {a, b} + descendents(a) + descendents(b)
    }
}

function child_descendents(e: Expression) : (cd_flat: set<Expression>)
    ensures flatten(set i | i in children(e) :: descendents(i)) <= descendents(e)
    ensures cd_flat == flatten(set i | i in children(e) :: descendents(i))
{
    child_descendents_helper(e, descendents(e))
}

function child_descendents_helper(e: Expression, d: set<Expression>) : (cd_flat: set<Expression>)
    requires d == descendents(e)
    ensures flatten(set i | i in children(e) :: descendents(i)) <= d
    ensures cd_flat == flatten(set i | i in children(e) :: descendents(i))
{
    assert forall i :: i in children(e) ==> descendents(i) < d;
    assert e !in d;

    var cs := children(e);
    assert forall i :: i in cs ==> descendents(i) < d;
    assert cs == children(e);
    var cd_flat := flatten(set i | i in cs :: descendents(i));
    assert cd_flat == flatten(set i | i in children(e) :: descendents(i));
    assert cd_flat + cs == d;
    assert cd_flat <= d;
    cd_flat
}

function height(e: Expression) : (h: int)
    decreases e
    ensures h >= 0
    ensures forall i :: i in children(e) ==> h > height(i)
{       
    match e {
        case Constant(b) => 0
        case Var(v) => 0
        case Not(e) => height(e) + 1
        case And(s) =>
            if |s| == 0 then
                0
            else
                assert s == children(e);
                var heights_set := set i | i in s :: height(i);
                var heights_map := map i | i in s :: height(i);
                assert forall i :: i in s ==> height(i) in heights_set;
                assert forall i :: i in s ==> i in heights_map.Keys;
                assert forall i :: i in s ==> height(i) in heights_map.Values;
                assert heights_set == heights_map.Values;
                notempty(s, heights_map);
                var max_child := max(heights_set);
                var h := max_child + 1;
                assert forall i :: i in children(e) ==> h > height(i);
                h
        case Or(s) => 
            if |s| == 0 then
                0
            else
                assert s == children(e);
                var heights_set := set i | i in s :: height(i);
                var heights_map := map i | i in s :: height(i);
                assert forall i :: i in s ==> height(i) in heights_set;
                assert forall i :: i in s ==> i in heights_map.Keys;
                assert forall i :: i in s ==> height(i) in heights_map.Values;
                assert heights_set == heights_map.Values;
                notempty(s, heights_map);
                var max_child := max(heights_set);
                var h := max_child + 1;
                assert forall i :: i in children(e) ==> h > height(i);
                h
        case Implies(a,b) => max({height(a), height(b)}) + 1
        case Equivalent(a,b) => max({height(a), height(b)}) + 1
    }
}

function vars(e: Expression) : (vs: set<Variable>)
    decreases e, height(e)
    ensures forall i :: i in children(e) ==> vs >= vars(i)
{
    match e {
        case Constant(b) => {}
        case Var(v) => {v}
        case Not(e) => vars(e)
        case And(ands) => flatten(set a | a in ands :: vars(a))
        case Or(ors) => flatten(set o | o in ors :: vars(o))
        case Implies(a,b) => vars(a) + vars(b)
        case Equivalent(a,b) => vars(a) + vars(b)
    }
}
/*
function set_vars(s: set<Expression>) : (vs: set<Variable>)
    ensures forall i :: i in s ==> vars(i) <= vs
    ensures flatten(set i | i in s :: vars(i)) == vs
{
    flatten(set i | i in s :: vars(i))
}

lemma bigger_set_bigger_vars(a: set<Expression>, b: set<Expression>, av: set<Variable>, bv: set<Variable>)
    requires a <= b
    requires set_vars(a) == av && set_vars(b) == bv
    ensures av <= bv
{

}
/*

lemma descendent_vars(e: Expression, vs: set<Variable>)
    requires vars(e) == vs
    decreases height(e)
    //ensures forall i :: i in descendents(e) ==> vars(e) >= vars(i)
{
    assert forall i :: i in children(e) ==> vars(e) >= vars(i);
    var cs := children(e);
    var cds := flatten(set i | i in children(e) :: descendents(i));
    var ds := descendents(e);
    //assert cds < ds;

    var cds_vs := set_vars(cds);
    var ds_vs := set_vars(ds);

}

*/

function eval(e: Expression, vs: map<Variable,bool>) : bool
    requires vs.Keys >= vars(e)
    decreases e
{
    match e {
        case Constant(b) => b
        case Var(v) => vs[v]
        case Not(e) => !eval(e, vs)
        case And(ands) => forall a :: a in ands ==> eval(a, vs)
        case Or(ors) => !(forall o :: o in ors ==> !eval(o, vs))
        case Implies(a,b) => !eval(a, vs) || eval(b, vs)
        case Equivalent(a,b) => (eval(a, vs) && eval(b,vs)) || (!eval(a, vs) && !eval(b, vs))
    }
}

lemma demorgan1(s: set<Expression>, vs: map<Variable,bool>)
    requires forall i :: i in s ==> vs.Keys >= vars(i)
    ensures eval(Not(Or(s)), vs) == eval(And(set i | i in s :: Not(i)), vs)
{
    var x := eval(Not(Or(s)), vs);
    var or := Or(s);
    assert eval(or, vs) == (!forall i :: i in s ==> !eval(i, vs));
    assert x == !(!forall i :: i in s ==> !eval(i, vs));
    
    var y := eval(And(set i | i in s :: Not(i)), vs);
    var nots := set i | i in s :: Not(i);
    assert y == eval(And(nots), vs);
    assert eval(And(nots), vs) == (forall i :: i in nots ==> eval(i, vs));
    assert !(!forall i :: i in s ==> !eval(i, vs)) == (forall i :: i in s ==> eval(Not(i), vs));
}

lemma demorgan2(s: set<Expression>, vs: map<Variable,bool>)
    requires forall i :: i in s ==> vs.Keys >= vars(i)
    ensures eval(Not(And(s)), vs) == eval(Or(set i | i in s :: Not(i)), vs)
{
    var x := eval(Not(And(s)), vs);
    var and := And(s);
    assert eval(and, vs) == (!forall i :: i in s ==> !eval(i, vs));
    assert x == !(!forall i :: i in s ==> !eval(i, vs));
    
    var y := eval(Or(set i | i in s :: Not(i)), vs);
    var nots := set i | i in s :: Not(i);
    assert y == eval(Or(nots), vs);
    assert eval(Or(nots), vs) == (forall i :: i in nots ==> eval(i, vs));
    assert !(!forall i :: i in s ==> !eval(i, vs)) == (forall i :: i in s ==> eval(Not(i), vs));
}

function method simplify_one(e: Expression, vs: map<Variable,bool>) : (out: Expression)
    requires vs.Keys >= vars(e)
    decreases e
    ensures match out {
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
    ensures vars(e) >= vars(out)
    ensures eval(e, vs) == eval(out, vs)
{
    match e {
        case Implies(a,b) => Or({Not(a), b})
        case Equivalent(a,b) => 
            var both_true := And({a,b});
            assert eval(both_true, vs) == (eval(a, vs) && eval(b, vs));
            var both_false := And({Not(a),Not(b)});
            assert vars(both_false) <= vars(e);
            assert eval(both_false, vs) == (!eval(a, vs) && !eval(b, vs));
            var out := Or({both_true, both_false});
            assert vars(out) <= vars(e);
            assert eval(e, vs) == eval(out, vs);
            out
        case Not(n) =>
            var out := match n {
                case Or(s) =>
                    descendents_vars(e, vs);
                    demorgan1(s, vs);
                    And(set i | i in s :: Not(i))
                case And(s) =>
                    descendents_vars(e, vs);
                    demorgan2(s, vs);
                    Or(set i | i in s :: Not(i))
                case _ => e
            };
            assert eval(e, vs) == eval(out, vs);
            out
        case e => e
    }
}

predicate no_implies(e: Expression) {
    forall i :: i in {e} + descendents(e) ==> match i {
        case Implies(_,_) => false 
        case e => true
    }
}

function method simplify_implies(e: Expression, vs: map<Variable,bool>) : (out: Expression)
    requires vs.Keys >= vars(e)
    decreases e
    ensures no_implies(out)
    ensures vars(e) >= vars(out)
    ensures eval(e, vs) == eval(out, vs)
{
    descendents_vars(e, vs);
    var out := match e {
        case Constant(b) =>
            assert no_implies(e);
            e
        case Var(v) =>
            assert no_implies(e);
            e
        case Not(x) => 
            var xx := simplify_implies(x, vs);
            assert no_implies(xx);
            assert no_implies(Not(xx));
            Not(xx)
        case And(s) => 
            var ss := set i | i in s :: simplify_implies(i, vs);
            assert forall i :: i in ss ==> no_implies(i);
            assert no_implies(And(ss));
            And(ss)
        case Or(s) =>
            var ss := set i | i in s :: simplify_implies(i, vs);
            assert forall i :: i in ss ==> no_implies(i);
            assert no_implies(Or(ss));
            Or(ss)
        case Implies(a,b) => 
            var a:= simplify_implies(a, vs);
            assert no_implies(a) && no_implies(Not(a));
            var b := simplify_implies(b, vs);
            assert no_implies(b);
            assert no_implies(Or({Not(a), b}));
            Or({Not(a), b})
        case Equivalent(a,b) => 
            var a:= simplify_implies(a, vs);
            assert no_implies(a);
            var b := simplify_implies(b, vs);
            assert no_implies(b);
            assert no_implies(Equivalent(a, b));
            Equivalent(a, b)
    };

    out
}

predicate no_equivalent(e: Expression) {
    forall i :: i in {e} + descendents(e) ==> match i {
        case Equivalent(_,_) => false 
        case e => true
    }
}

function method simplify_equivalent(e: Expression, vs: map<Variable,bool>) : (out: Expression)
    requires vs.Keys >= vars(e)
    requires no_implies(e)
    decreases e
    ensures no_equivalent(out)
    ensures vars(e) >= vars(out)
    ensures eval(e, vs) == eval(out, vs)
{
    descendents_vars(e, vs);
    var out := match e {
        case Constant(b) =>
            assert no_equivalent(e);
            e
        case Var(v) =>
            assert no_equivalent(e);
            e
        case Not(x) => 
            var xx := simplify_equivalent(x, vs);
            assert no_equivalent(xx);
            assert no_equivalent(Not(xx));
            Not(xx)
        case And(s) => 
            var ss := set i | i in s :: simplify_equivalent(i, vs);
            assert forall i :: i in ss ==> no_equivalent(i);
            assert no_equivalent(And(ss));
            And(ss)
        case Or(s) =>
            var ss := set i | i in s :: simplify_equivalent(i, vs);
            assert forall i :: i in ss ==> no_equivalent(i);
            assert no_equivalent(Or(ss));
            Or(ss)
        case Implies(a,b) => 
            assert false;
            a
        case Equivalent(a,b) => 
            var a:= simplify_equivalent(a, vs);
            assert no_equivalent(a);
            var b := simplify_equivalent(b, vs);
            assert no_equivalent(b);
            var out := Or(And({a,b}),And({Not(a),Not(b)}));
            assert no_implies(out);
            out
    };

    out
}

predicate no_not_expressions(e: Expression) {
    forall i :: i in {e} + descendents(e) ==> match i {
        case Not(n) => match n {
            case Var(_) => true
            _ => false
        }
        case e => true
    }
}

function method simplify_not_expressions(e: Expression, vs: map<Variable,bool>) : (out: Expression)
    requires vs.Keys >= vars(e)
    requires no_implies(e)
    requires no_equivalent(out)
    decreases e
    ensures no_not_expressions(out)
    ensures vars(e) >= vars(out)
    ensures eval(e, vs) == eval(out, vs)
{
    descendents_vars(e, vs);
    var out := match e {
        case Constant(b) =>
            assert no_not_expressions(e);
            e
        case Var(v) =>
            assert no_not_expressions(e);
            e
        case Not(x) => 
            var xx := match x {
                case Constant(b) =>
                    Constant(!b)
                case Var(v) =>
                    Not(x)
                case Not(xx) =>
                    var xxx := simplify_not_expressions(xx, vs);
                    xxx
                case And(s) =>
                    var ss := set i | i in s :: simplify_not_expressions(i, vs);
                    assert forall i :: i in ss ==> no_not_expressions(i);
                    descendents_vars(e, vs);
                    demorgan2(ss, vs);
                    var xx := Or(set i | i in ss :: Not(i));
                    assert no_not_expressions(xx);
                    xx
                case Or(s) =>
                    var ss := set i | i in s :: simplify_not_expressions(i, vs);
                    assert forall i :: i in ss ==> no_not_expressions(i);
                    descendents_vars(e, vs);
                    demorgan1(ss, vs);
                    var xx := And(set i | i in ss :: Not(i));
                    assert no_not_expressions(xx);
                    xx
                case Implies(a,b) => 
                    assert false;
                    a
                case Equivalent(a,b) => 
                    assert false;
                    a
            };
            assert no_not_expressions(xx);
            xx
        case And(s) => 
            var ss := set i | i in s :: simplify_not_expressions(i, vs);
            assert forall i :: i in ss ==> no_not_expressions(i);
            assert no_not_expressions(And(ss));
            And(ss)
        case Or(s) =>
            var ss := set i | i in s :: simplify_not_expressions(i, vs);
            assert forall i :: i in ss ==> no_not_expressions(i);
            assert no_not_expressions(Or(ss));
            Or(ss)
        case Implies(a,b) => 
            assert false;
            a
        case Equivalent(a,b) => 
            assert false;
            a
    };

    out
}

function method simplify(e: Expression, vs: map<Variable,bool>) : (out: Expression)
    requires vs.Keys >= vars(e)
    ensures no_implies(out)
    ensures no_equivalent(out)
{
    var out := simplify_implies(e, vs);
    var out := simplify_equivalent(e, vs);
    out
}