include "util.dfy"

//Provably correct SAT solver
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

function vars(e: Expression) : set<Variable>
    decreases e, height(e)
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

lemma demorgan(s: set<Expression>, vs: map<Variable,bool>)
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

method simplify(e: Expression, vs: map<Variable,bool>) returns (out: Expression)
    requires vs.Keys >= vars(e)
    decreases e
    ensures match out {
        case Implies(_,_) => false 
        case Equivalent(_,_) => false
        case Not(ee) =>
            match ee {
                case Or(_) => false
                case _ => true
            }
        case e => true
    }
    ensures vars(e) >= vars(out)
    ensures eval(e, vs) == eval(out, vs)
{
    match e {
        case Implies(a,b) => {
            out := Or({Not(a), b});
        }
        case Equivalent(a,b) => {
            var both_true := And({a,b});
            assert eval(both_true, vs) == (eval(a, vs) && eval(b, vs));
            var both_false := And({Not(a),Not(b)});
            assert vars(both_false) <= vars(e);
            assert eval(both_false, vs) == (!eval(a, vs) && !eval(b, vs));
            out := Or({both_true, both_false});
            assert vars(out) <= vars(e);
            assert eval(e, vs) == eval(out, vs);
        }
        case Not(n) => {
            out := match n {
                case Or(s) =>
                    demorgan(s, vs);
                    And(set i | i in s :: Not(i))
                case _ => e
            };
            assert eval(e, vs) == eval(out, vs);
        }
        case e => out := e;
    }
}
