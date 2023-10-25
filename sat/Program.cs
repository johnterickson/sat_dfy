
using SAT;

internal class Program
{
    private static int Main(string[] args)
    {
        var parsed = new Stack<_IExpression>();
        foreach(var arg in args)
        {
            if (arg == "true" || arg == "T") {
                parsed.Push(new Expression_Constant(true));
            } else if (arg == "false" || arg == "F") {
                parsed.Push(new Expression_Constant(false));  
            } else if (arg == "or" || arg == "|") {
                parsed.Push(new Expression_Or(parsed.Pop(), parsed.Pop()));
            } else if (arg == "and" || arg == "&") {
                parsed.Push(new Expression_And(parsed.Pop(), parsed.Pop()));
            } else if (int.TryParse(arg, out int varNum)) {
                parsed.Push(new Expression_Var(new System.Numerics.BigInteger(Math.Abs(varNum)), varNum < 0));
            } else {
                Console.WriteLine("huh? " + arg);
                return 1;
            }
        }

        _IExpression exp = parsed.Pop();
        _ICNFResult cnfr = exp.make__cnf();
        if (cnfr is CNFResult_ConstantResult constantResult)
        {
            Console.WriteLine("Constant: " + constantResult._a0);
        }
        else if (cnfr is CNFResult_VariableResult cnfvr) 
        {
            var cnf = cnfvr._a0;
            cnf = CNF.__default.cnf__remove__tautologies(cnf);
            foreach(var c in cnf.Elements)
            {
                Console.Write("Clause: ");
                bool first = true;
                foreach (_IClauseLit l in c.Elements)
                {
                    if (first) {
                        first = false;
                    } else {
                        Console.Write(" or ");
                    }
                    Console.Write(l);
                }
                Console.WriteLine();
            }
        }

        return 0;
    }
}