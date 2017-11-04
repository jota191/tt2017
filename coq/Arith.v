(****************************************************************************)
(* In this module I implement excercises 28, 29, 30 (....)                  *)
(* I started to do this in phox, I will show you what did I implement       *)
(* if you wish. Since my sheet is a bit under overdue, switched to coq      *)
(* where I know I will finish faster                                        *)

(* 

Instead of embed HOL in coq or define stuff over the coq constructions,
I define every theorem we use as an axiom. For example I use:

0 + n = n
S n + m = S(n + m)

as axioms instead of define N and derive them.
This will be enough since that theorems are proved when the excercises are
asked
*)

Module hol.


(* I define the Variable N, Type will be the sort omicron (It doesn't care 
too much) 
*)

Parameter N : Type.
Variable O : N.
Variable S : N -> N.


Delimit Scope HOLScope with my.
(* These are actually axioms in HOL already*)

Axiom S_inj: forall n m :N, n <> m -> S m <> S n.
Axiom O_not_S: forall n :N, O <> S n.


Variable Add : N -> N -> N.
Infix "+" := Add.


Axiom add_O : forall x y : N, (S x)+ y = S (x + y).
Axiom add_S : forall x y : N, O + y = y.


Axiom Nat_ind: 
forall P: N -> Prop, P O -> (forall n:N, P n -> P(S n)) -> forall n:N, P n.

Theorem nat_conm : forall n m: N, (n+m) = (m + n).
intro.
apply Nat_ind.








