(* oracle.ml
   Calculus problem-solver
   It can do: derivatives, linear algebra, simplification/evaluation,

   TODO:
   Finish trig and log wonkiness --e^x, n^x
   Do inverse (trig/log) functions

   Double-check integrals
   Do limits?
   Do algebraic equations?  isolate a var, etc.


   Non-direct-math functions --applications:
   Finding critical points of a function
   Graphing

   Maybe make a UI complete with parser?
   Staple it to the math department

   Hours invested in this: 2.0

   Simon Heath
   16/11/2005
*)

open Printf;;

exception MathException of string;;

(* This is the type of our mathematical expression-tree 
   We just express negative functions as Sub( zero, whatever )
   We might need: Sec, Csc, Cot (but then transformation is wiggy)
   Logn(x) (same), inverse trig funcs.
*)
type t =
    Num of float
  | Var of string

  | Add of t * t
  | Sub of t * t
  | Mul of t * t
  | Div of t * t
 
  | Pow of t * t
  | Exp of t
  | Ln of t

  | Sin of t
  | Cos of t
  | Tan of t
;;

type eqn = t * t;;

(* Handy constants and helper functions *)
let pi = Num( 3.1415926 )
and e = Num( 2.7182818 ) 
and one = Num( 1. )
and zero = Num( 0. );;
let negone = Sub( zero, one )
;;

let isNum = function
    Num( x ) -> true
  | a -> false
;;

let isVar = function
    Var( x ) -> true
  | a -> false
;;

let isFunc = function
    Num( x ) -> false
  | Var( x ) -> false
  | a -> true
;;

let stripNum = function
    Num( x ) -> x
  | _ -> raise (MathException "stripNum: Not given a num!")
;;

(* Basic derivatives *)
let rec deriv = function
    Add( x, y ) -> Add( deriv x, deriv y )
  | Sub( x, y ) -> Sub( deriv x, deriv y )
  | Mul( x, y ) -> Add( Mul( deriv x, y ), Mul( deriv y, x ) )
  | Div( x, y ) -> Div( Sub( Mul( deriv x, y ), Mul( deriv y, x ) ),
			Pow( y, Num( 2. ) ) )
  | Num( x ) -> Num( 0. )
  | Var( _ ) -> Num( 1. )

      (* XXX: This won't work for, say, n^x --change to exp first? *)
  | Pow( x, y ) -> 
      if isFunc x then chain (Pow( x, y ))
      else Mul( y, Pow( x, Sub( y, one ) ) )
  | Exp( x ) -> Exp( x )
  | Ln( x ) -> 
      if isFunc x then chain (Ln( x ))
      else Div( one, Mul( e, x ) )

  | Sin( x ) ->
      if isFunc x then chain (Sin( x ))
      else Cos( x )
  | Cos( x ) ->
      if isFunc x then chain (Cos( x ))
      else Sub( zero, Sin( x ) )
  | Tan( x ) ->
      if isFunc x then chain (Tan( x ))
      else Mul( Div( one, Tan( x ) ), Div( one, Tan( x ) ) )

(* Chain rule! *)
and chain = function
    Add( x, y ) -> Add( x, y )
  | Sub( x, y ) -> Sub( x, y )
  | Mul( x, y ) -> Add( Mul( deriv x, y ), Mul( deriv y, x ) )
  | Div( x, y ) -> Div( Sub( Mul( deriv x, y ), Mul( deriv y, x ) ),
			Pow( y, Num( 2. ) ) )
  | Num( x ) -> Num( x )
  | Var( x ) -> Var( x )

  | Pow( x, y ) -> Mul( Mul( y, Pow( x, Sub( y, one ) ) ), deriv x )
  | Exp( x ) -> Exp( x ) (* XXX *)
  | Ln( x ) -> Mul( Div( one, x ), deriv x )

  | Sin( x ) -> Mul( Cos( x ), deriv x )
  | Cos( x ) -> Mul( Sub( zero, Sin( x ) ), deriv x )
  | Tan( x ) -> Mul( Mul( Div( one, Tan( x ) ), Div( one, Tan( x ) ) ),
                deriv x )
;;

(* Hrm.  Slight technical issue here.  it's not integral( f(x) ), it's
   integral( f(x)dx ).  The dx, we don't represent...
   ...hm.  It would appear that this is decidedly non-trivial at the best of 
   times.
   XXX: We also need something resembling a chain rule, I think...
*)
let rec antideriv = function
    Add( x, y ) -> Add( antideriv x, antideriv y )
  | Sub( x, y ) -> Sub( antideriv x, antideriv y )
  | Mul( x, y ) -> (* Is this right?  Probably not... *)
      if isNum x then
	Mul( x, antideriv y )
      else if isNum y then
	Mul( y, antideriv x )
      else
	Sub( Mul( x, antideriv y ), antideriv (Mul( deriv x, y )) )
      
  (* There doesn't seem to be any general-case division... 
     Perhaps we can turn it into foo^-1?
  *)
  | Div( x, y ) -> 
      if x = one && isVar y then
	Add( Ln( y ), Var( "c" ) )
      else
	raise (MathException "Integrating arbitrary division is impossible!" )
	    
  | Num( x ) -> Num( x )
  | Var( x ) -> Add( Var( x ), Var( "c" ) )

  | Pow( x, y ) ->
      if y <> negone then
	Add( Div( Pow( x, Add( y, one ) ), Add( y, one ) ), Var( "c" ) )
      else
	raise (MathException "Power integral produces 0/0!")
  | Exp( x ) -> Add( Exp( x ), Var( "c" ) )
  | Ln( x ) -> Add( Sub( Mul( x, Ln( x ) ), x ), Var( "c" ) )

  | Sin( x ) -> Add( Sub( zero, Cos( x ) ), Var( "c" ) )
  | Cos( x ) -> Add( Sin( x ), Var( "c" ) )
  | Tan( x ) -> Add( Sub( zero, Ln( Cos( x ) ) ), Var( "c" ) )
;;

    

(* There's probably a nicer way to do this --code duplication-- but
   oh well.

   ...hm.  It's possible that it will try to re-simplify things a lot
   when it isn't necessary, when given indeterminate forms.
   Add( x, 5 ) will return Add( x, 5 ), and everything that gets it
   will try to simplify it again.
   Oh well!

   This could also try to be a bit smarter, like realizing x/x = 1 and such.
*)
let rec simplify = function
    Add( x, y ) -> 
      let a = simplify x
      and b = simplify y in
	if isNum a && isNum b then
	  let x1, y1 = (stripNum a), (stripNum b) in
	    Num( x1 +. y1 )
	else
	  Add( a, b )

  | Sub( x, y ) -> 
      let a = simplify x
      and b = simplify y in
	if isNum a && isNum b then
	  let x1, y1 = (stripNum a), (stripNum b) in
	    Num( x1 -. y1 )
	else
	  Sub( a, b )

  | Mul( x, y ) -> 
      let a = simplify x
      and b = simplify y in
	if isNum a && isNum b then
	  let x1, y1 = (stripNum a), (stripNum b) in
	    Num( x1 *. y1 )
	else
	  Mul( a, b )

  | Div( x, y ) -> 
      let a = simplify x
      and b = simplify y in
	if isNum a && isNum b then
	  let x1, y1 = (stripNum a), (stripNum b) in
	    Num( x1 /. y1 )
	else
	  Div( a, b )


  | Num( x ) -> Num( x )
  | Var( x ) -> Var( x )

  | Pow( x, y ) ->
      let a = simplify x
      and b = simplify y in
	if isNum a && isNum b then
	  let x1, y1 = (stripNum a), (stripNum b) in
	    Num( x1 ** y1 )
	else
	  Pow( a, b )


  (* Here it gets more complicated, 'cause things mix up.  Ugh. 
     XXX: Do they?
  *)
  | Exp( x ) -> 
      let a = simplify x in
	if isNum a then
	  let x1 = stripNum a in
	    Num( exp x1 )
	else
	  Exp( a )

  | Ln( x ) -> 
      let a = simplify x in
	if isNum a then
	  let x1 = stripNum a in
	    Num( log x1 )
	else
	  Ln( a )

  | Sin( x ) ->
      let a = simplify x in
	if isNum a then
	  let x1 = stripNum a in
	    Num( sin x1 )
	else
	  Sin( a )

  | Cos( x ) ->
      let a = simplify x in
	if isNum a then
	  let x1 = stripNum a in
	    Num( cos x1 )
	else
	  Cos( a )

  | Tan( x ) ->
      let a = simplify x in
	if isNum a then
	  let x1 = stripNum a in
	    Num( tan x1 )
	else
	  Tan( a )
;;


(* Evaluates an expression --replaces all the instances of var with vl,
   then simplifies it.
   vl is a term; thus, you can chain these together to do linear algebra!
*)
let rec replaceVar var vl = function
    Add( x, y ) -> Add( (replaceVar var vl x), (replaceVar var vl y) )
  | Sub( x, y ) -> Sub( (replaceVar var vl x), (replaceVar var vl y) )
  | Mul( x, y ) -> Mul( (replaceVar var vl x), (replaceVar var vl y) )
  | Div( x, y ) -> Div( (replaceVar var vl x), (replaceVar var vl y) )

  | Num( x ) -> Num( x )
      (* This is where the magic happens *)
  | Var( a ) -> if a = var then vl else Var( a )

  | Pow( x, y ) -> Pow( (replaceVar var vl x), (replaceVar var vl y) )

  | Exp( x ) -> Exp( (replaceVar var vl x) )
  | Ln( x ) -> Ln( (replaceVar var vl x) )

  | Sin( x ) -> Sin( (replaceVar var vl x) )

  | Cos( x ) -> Cos( (replaceVar var vl x) )

  | Tan( x ) -> Tan( (replaceVar var vl x) )

and evaluate term var vl =
  simplify (replaceVar var vl term)
;;

(* Takes an antiderivative, computes the integral of it at the given points *)
let defIntegral term var x1 x2 =
  let a = (evaluate term var x1)
  and b = (evaluate term var x2) in
    simplify (Sub( a, b ))
;;


let rec varExists term varname =
  match term with
      Add( x, y ) -> (varExists x varname) || (varExists y varname)
    | Sub( x, y ) -> (varExists x varname) || (varExists y varname)
    | Mul( x, y ) -> (varExists x varname) || (varExists y varname)
    | Div( x, y ) -> (varExists x varname) || (varExists y varname)

    | Num( x ) -> false
    | Var( a ) -> a = varname 

    | Pow( x, y ) -> (varExists x varname) || (varExists y varname)

    | Exp( x ) -> (varExists x varname)
    | Ln( x ) ->  (varExists x varname)

    | Sin( x ) -> (varExists x varname)
    | Cos( x ) -> (varExists x varname)
    | Tan( x ) -> (varExists x varname)

;;


(* Hmm, instead of transforming both sides of an equation, we can just make 
   a series of operations --a function that will, when simplified, convert
   one side to the desired form

   This doesn't quiiiiiite work right.  For one thing, it tends to 
   come up with things the simplifier can't (easily) simplify.  For another,
   it doesn't actually try to ISOLATE the variable as such.
   I think that if the simplifier were perfect, this would work fine,
   but...
*)
let rec makeInverseFunc fnc =
  match fnc with
      Add( x, y ) -> Sub( makeInverseFunc x, makeInverseFunc y )
    | Sub( x, y ) -> Add( makeInverseFunc x, makeInverseFunc y )
    | Mul( x, y ) -> Div( makeInverseFunc x, makeInverseFunc y )
    | Div( x, y ) -> Mul( makeInverseFunc x, makeInverseFunc y )

    | Num( x ) -> Num( x )
    | Var( a ) -> Var( a )

    | Pow( x, y ) -> Sub( makeInverseFunc x, makeInverseFunc y )

    | Exp( x ) -> Ln( makeInverseFunc x )
    | Ln( x ) -> Exp( makeInverseFunc x )

    | Sin( x ) -> raise (MathException "We don't do inverse trig yet!")
    | Cos( x ) -> raise (MathException "We don't do inverse trig yet!")
    | Tan( x ) -> raise (MathException "We don't do inverse trig yet!")
;;

(* This performs algebraic stuff, isolating a variable on one side.
   It's not necessarily too smart about it, but we have number-crunching
   power to spare.

   XXX: It doesn't work, and I dun wanna bother.
*)

let isolateVar eqn var =
    let lhs, rhs = eqn in
    let iv = makeInverseFunc lhs in
    let nlhs = evaluate iv var lhs
    and rhs = evaluate iv var rhs in
      (lhs, rhs)
;;





let rec toString = function
    Add( x, y ) -> sprintf "(%s+%s)" (toString x) (toString y)
  | Sub( x, y ) -> sprintf "(%s-%s)" (toString x) (toString y)
  | Mul( x, y ) -> sprintf "(%s*%s)" (toString x) (toString y)
  | Div( x, y ) -> sprintf "(%s/%s)" (toString x) (toString y)

  | Num( x ) -> sprintf "%0.0f" x
  | Var( x ) -> x

  | Pow( x, y ) -> sprintf "(%s^%s)" (toString x) (toString y)
  | Exp( x ) -> sprintf "(e^%s)" (toString x)
  | Ln( x ) -> sprintf "(ln %s)" (toString x)

  | Sin( x ) -> sprintf "(sin %s)" (toString x)
  | Cos( x ) -> sprintf "(cos %s)" (toString x)
  | Tan( x ) -> sprintf "(tan %s)" (toString x)
;;

let eqnToString x =
  let lhs, rhs = x in
    (toString lhs) ^ " = " ^ (toString rhs)
;;

let printDeriv x =
  print_endline (toString (deriv x))
;;

let printSimp x =
  print_endline (toString (simplify x))
;;

let printSD x =
  print_endline (toString (simplify (deriv x)))
;;

let a = Pow( Var( "x" ), Num( 3. ) );;

let b = Sin( Cos( Var( "x" ) ) );;
let c = Tan( Cos( Var( "y" ) ) );;
let e1 = (Var("y"), a );;
let e2 = (Add( Mul( Var( "x" ), Var( "y" ) ), Num( 5. ) ),
	  Sub( Var( "x" ), Num( 12. ) ));;


let f = Ln( Div( Sub( Mul( Num( 4 ), Var( "x" ) ), Num( 4 ) ),
                 Mul(  
