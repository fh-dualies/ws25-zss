datatype List<T> = Nil | Cons(head: T, tail: List<T>)
datatype Op = Add | Mul
datatype Expr = Const(nat) | Var(string) | Node(op: Op, args:List<Expr>)

function Eval(e: Expr, env: map<string, nat>): nat {
    match e
    case Const(c) => c
    case Var(s) => if s in env.Keys then env[s] else 0
    case Node(op, args) => EvalList(args, op, env)
}

function applyOp(op: Op, one: nat, two: nat) : nat {
  match op
  case Add => one + two
  case Mul => one * two
}

function EvalList(args: List<Expr>, op: Op, env: map<string, nat>) : nat {
    match args
    case Nil =>
            match op {
            case Add => 0
            case Mul => 1
            }
    case Cons(e, tail) => 
        var v0 := Eval(e, env);
        var v1 := EvalList(tail, op, env);
        applyOp(op, v0, v1)
}    

/** replaces a variable n by constant c */
function Substitute(e: Expr, n: string, c:nat):Expr
{
    match e
    case Const(_) => e
    case Var(s) => if s == n then Const(c) else e
    case Node(op, args) => Node(op, SubstituteList(args, n, c))
}

function SubstituteList(es: List<Expr>, n: string, c:nat): List<Expr>
{
    match es
    case Nil => Nil
    case Cons(e, tail) => Cons(Substitute(e, n, c), SubstituteList(tail, n, c))
}


lemma{:induction false} EvalEnvDefault(e: Expr, n:string, env:map<string, nat>)
requires n !in env.Keys
ensures Eval(e, env) == Eval(Substitute(e, n, 0), env)
{
    match e
    case Node(op, args) => {
        calc {
            EvalList(args, op, env);
            == {EvalListEnvDefault(args, op, n, env);}
            EvalList(SubstituteList(args, n, 0), op, env);
            ==
            Eval(Substitute(e, n, 0), env);
        }
    }
    case Const(c) => {
        calc {
            Eval( Const(c), env );
            ==
            c;
            ==
            Eval( Substitute( Const(c), n, 0), env );
        }
    }
    case Var(s) => {
        if s == n {
            calc {
                Eval( Var(s), env );
                ==
                0;
                ==
                Eval( Substitute( Var(s), n, 0), env );
            }
        } else {
            if s !in env.Keys {
                calc {
                    Eval( Var(s), env );
                    ==
                    0;
                    ==
                    Eval( Substitute( Var(s), n, 0), env );
                }
            } else {
                calc {
                    Eval( Var(s), env );
                    ==
                    env[s];
                    ==
                    Eval( Substitute( Var(s), n, 0), env );
                }
            }
        }
    }
}

lemma{:induction false} EvalListEnvDefault(args: List<Expr>, op: Op, n:string, env: map<string, nat>)
requires n !in env.Keys
ensures EvalList(args, op, env) == EvalList(SubstituteList(args, n, 0), op, env)
{
    match args
    case Nil => {
        calc {
            EvalList(Nil, op, env);
            ==
            EvalList(SubstituteList(Nil, n, 0), op, env);
        }
    }
    case Cons(e, tail) => {
        calc {
            EvalList(Cons(e, tail), op, env);
            ==
            applyOp(op, Eval(e, env), EvalList(tail, op, env));
            == {EvalEnvDefault(e, n, env); EvalListEnvDefault(tail, op, n, env);}
            applyOp(op, Eval(Substitute(e, n, 0), env), EvalList(SubstituteList(tail, n, 0), op, env));
            ==
            EvalList(Cons(Substitute(e, n, 0), SubstituteList(tail, n, 0)), op, env);
            ==
            EvalList(SubstituteList(Cons(e, tail), n, 0), op, env);
        }
    }
}
