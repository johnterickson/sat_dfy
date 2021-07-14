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

predicate valid(e: Expression) 
    decreases e
{
    match e {
        case Constant(b) => true
        case Var(v) => true
        case Not(e) => valid(e)
        case And(ands) => |ands| >= 1 && forall a :: a in ands ==> valid(a)
        case Or(ors) => |ors| >= 1 && forall o :: o in ors ==> valid(o)
        case Implies(a,b) => valid(a) && valid(b)
        case Equivalent(a,b) => valid(a) && valid(b)
    }
}

function flatten<T>(nested: set<set<T>>) : set<T>
{
    set x, y | y in nested && x in y :: x
}

function pick(s: set<int>): (x: int)
  requires s != {}
  ensures |s| == 1 ==> {x} == s
{
    var x :| x in s; 
    assert x in s;
    if |s| == 1 then 
        var remainder := s - {x};
        assert |remainder| == 0;
        assert remainder == {};
        assert remainder + {x} == s;
        assert {x} == s;
        x
    else
        x
}

function max(s: set<int>) : (m: int)
    requires |s| >= 1
    decreases s
    ensures m in s
    ensures forall i :: i in s ==> m >= i
{
    var x := pick(s);
    if |s| == 1 then
        assert forall i :: i in s ==> x >= i;
        x
    else 
        var remainder := s - {x};
        var y:int := max(remainder);
        if (x >= y) then 
            assert forall i :: i in remainder ==> y >= i;
            assert forall i :: i in remainder ==> x >= i;
            assert s == {x} + remainder;
            assert forall i :: i in s ==> x >= i;
            x
        else 
            assert forall i :: i in s ==> y >= i;
            y
}

lemma notempty<K,V>(s: set<K>, m: map<K,V>)
    requires s == m.Keys
    ensures |s| == |m|
    ensures |s| >= 1 ==> |m| >= 1
{}

function height(e: Expression) : int
    requires valid(e)
    decreases e
{       
    match e {
        case Constant(b) => 1
        case Var(v) => 1
        case Not(e) => height(e) + 1
        case And(ands) => 
            var heights := map a | a in ands :: height(a);
            notempty(ands, heights);
            max(heights.Values)
        case Or(ors) => 
            var heights := map o | o in ors :: height(o);
            notempty(ors, heights);
            max(heights.Values)
        case Implies(a,b) => max({height(a), height(b)})
        case Equivalent(a,b) => max({height(a), height(b)})
    }
}

function vars(e: Expression) : set<Variable>
    requires valid(e)
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
    requires valid(e)
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

function method invert(e: Expression) : (out: Expression)
    requires valid(e)
    ensures valid(out)
{
    Not(e)
}

function method and(es: set<Expression>) : (out: Expression)
    requires |es| >= 1
    requires forall e :: e in es ==> valid(e)
    ensures valid(out)
{
    And(es)
}

method simplify(e: Expression, vs: map<Variable,bool>) returns (out: Expression)
    requires valid(e)
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
    ensures valid(out)
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
            assert valid(both_false);
            assert vars(both_false) <= vars(e);
            assert eval(both_false, vs) == (!eval(a, vs) && !eval(b, vs));
            out := Or({both_true, both_false});
            assert valid(out);
            assert vars(out) <= vars(e);
            assert eval(e, vs) == eval(out, vs);
        }
        case Not(n) => {
            out := match n {
                case Or(ors) =>
                    assert forall i :: i in ors ==> valid(i);
                    var negs := map o | o in ors :: invert(o);
                    assert forall i :: i in ors ==> i in negs;
                    assert |negs| >= 1;
                    assert forall i :: i in negs.Values ==> valid(i);
                    and(negs.Values)
                case _ => e
            };
        }
        case e => out := e;
    }
}
