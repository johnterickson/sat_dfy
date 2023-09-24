include "sat.dfy"

datatype Expression2 =
    Constant2(bool) |
    Var2(Variable, bool) |
    And2(Expression2, Expression2) |
    Or2(Expression2,Expression2)
{
    static function from_Expression(e: Expression) : (ee: Expression2)
        requires e.Valid()
        requires e.no_implies()
        requires e.no_equivalent()
        requires e.no_not()
        ensures ee.Valid()
        ensures forall vs : map<Variable, bool> :: true ==>
            e.eval(vs) == ee.eval(vs)
    {
        match e {
            case Constant(b) => Constant2(b)
            case Var(v, i) => Var2(v, i)
            case And(a,b) => And2(from_Expression(a),from_Expression(b))
            case Or(a,b) => Or2(from_Expression(a),from_Expression(b))
            case Not(_) | Implies(_,_) | Equivalent(_,_) => 
                assert false; Constant2(false)
        }
    }

    function children() : (cs: set<Expression2>)
    {
        match this {
            case Constant2(b) => {}
            case Var2(v, _) => {}
            case And2(a,b) => {a, b}
            case Or2(a,b) => {a, b}
        }
    }
    
    ghost function height() : (h: int)
        ensures h >= 1
    {
        match this {
            case Constant2(b) => 1
            case Var2(v, _) => 1
            case And2(a,b) => 1 + max(a.height(), b.height())
            case Or2(a,b) => 1 + max(a.height(), b.height())
        }
    }

    ghost predicate Valid()
    {
        forall i :: i in children() ==> i.Valid() && i.height() < this.height()
    }

    function eval(vs: map<Variable,bool>) : (b: bool)
        requires this.Valid()
        decreases this
    {
        match this {
            case Constant2(b) => b
            case Var2(v, inverted) =>
                var val := if v in vs then vs[v] else false;
                if inverted then val else !val
            case And2(a,b) => a.eval(vs) && b.eval(vs)
            case Or2(a,b) => a.eval(vs) || b.eval(vs)
        }
    }
}