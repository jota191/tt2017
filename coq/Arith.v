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

(* 

we introduce this theorems as axioms, but they are proved from the definition
of Addition actually 

*)

Axiom add_S : forall x y : N, (S x)+ y = S (x + y).
Axiom add_O : forall y : N, O + y = y.


(*
again, this is proved from the definition of N, but here we use is as an axiom
*)

Axiom Nat_ind: 
forall P: N -> Prop, P O -> (forall n:N, P n -> P(S n)) -> forall n:N, P n.

Lemma O_add_conm : forall n:N, n = n + O.
Proof.
apply Nat_ind.
rewrite (add_O O).
trivial.
intros.
rewrite (add_S).
rewrite <- H.
reflexivity.
Qed.


Lemma add_S2 : forall n m : N, m + S n = S(m + n).
Proof.
intro.
apply Nat_ind.
rewrite (add_O).
rewrite add_O.
trivial.
intros.
rewrite add_S.
rewrite H.
rewrite add_S.
reflexivity.
Qed.


Theorem add_conm : forall n m: N, (n+m) = (m + n).
Proof.
intro.
apply Nat_ind.
rewrite <- O_add_conm.
rewrite (add_O n).
trivial.
intros.

rewrite add_S.
rewrite <-H.
apply (add_S2 n0 n).
Qed. 

(* Now we define product, again from equational axioms instead of derive them *)

Variable Mul : N -> N -> N.
Infix "*" := Mul.


Axiom mul_O : forall n:N, O * n = O.
Axiom mul_S : forall m n:N, (S m) * n = n + (m * n).



Lemma O_mul_conm : forall n:N, O = n * O.
Proof.
apply Nat_ind.
rewrite (mul_O O).
trivial.
intros.
rewrite (mul_S).
rewrite <- H.
rewrite (add_O O).
reflexivity.
Qed.


Lemma mul_S2 : forall n m : N, m * S n = m + (m * n).
Proof.
intro.
apply Nat_ind.
rewrite (mul_O).
rewrite add_O.
rewrite (mul_O).
trivial.
intro m.
intros.

rewrite mul_S.
rewrite add_S.
rewrite add_S.
rewrite mul_S.
rewrite H.

rewrite 

Qed.

Theorem mul_conm : forall n m:N, n * m = m * n.
Proof.
intro n.
apply Nat_ind.  







