(****************************************************************************)
(* In this module I implement excercises 28, 29, 30                         *)
(* I started to do this in phox, I will show you what did I implement       *)
(* if you wish. Since my sheet is under overdue, switched to coq            *)
(* where I know I will finish faster                                        *)
(* Instead of embed HOL in coq or define stuff over the coq constructions,  *)
(* I define every theorem we use as an axiom. For example I use:            *)
(*                                                                          *)
(* 0 + n = n                                                                *)
(* S n + m = S(n + m)                                                       *)
(*                                                                          *)
(* as axioms instead of define N and derive them.                           *)
(* This will be enough since that theorems are proved before                *)
(* the excercises are asked                                                 *)

Module Arith.


(* I define the Variable N, Type will be the sort iota, this doesn't care 
so much. Omicron will be Prop. Nothe that in Coq, Prop ∈ Type which is 
nonsense for HOL. We won't use this, so it won't be a problem  *)


Variable N : Type.
Variable O : N.
Variable S : N -> N.


(* These are actually axioms in HOL already *)

Axiom S_inj: forall n m :N, n <> m -> S m <> S n.
Axiom O_not_S: forall n :N, O <> S n.
Axiom S_inj_2 : forall m n : N, S m = S n -> m = n.
(* this could be derived of course *)


(* Define Adittion *) 
Variable Add : N -> N -> N.
Infix "+" := Add.

(* we introduce this theorems as axioms, but in HOL they are proved 
from the definition of Addition actually  *)

Axiom add_S : forall x y : N, (S x)+ y = S (x + y).
Axiom add_O : forall y : N, O + y = y.


(* The induction principle. Again, this is proved from the definition of N, *)
(* but here we use it as an axiom                                           *)

Axiom Nat_Ind: 
forall P: N -> Prop, P O -> (forall n:N, P n -> P(S n)) -> forall n:N, P n.

(* We prove some lemmas *)
(* The following two are the identities that are symetrical 
to the definitions *)

Lemma add_O_R_Identity : forall n:N, n = n + O.
Proof.
apply Nat_Ind.
rewrite (add_O O).
reflexivity.
intros.
rewrite (add_S).
rewrite <- H.
reflexivity.
Qed.


Lemma add_S_R : forall n m : N, m + S n = S(m + n).
Proof.
intro.
apply Nat_Ind.
rewrite (add_O).
rewrite add_O.
trivial.
intros.
rewrite add_S.
rewrite H.
rewrite add_S.
reflexivity.
Qed.


(* We are ready to prove the associativity of addition *)

Theorem add_assoc : forall m n k: N, ((n + m) + k =  n + (m + k)).
Proof.
intros m n.
apply Nat_Ind.
rewrite <- add_O_R_Identity.
rewrite <- add_O_R_Identity.
reflexivity.

intros k H.
rewrite add_S_R.
rewrite add_S_R.
rewrite add_S_R.
rewrite H.
reflexivity.
Qed.

(* Now we prove the conmutativity of addition *)

Theorem add_conm : forall n m: N, (n+m) = (m + n).
Proof.
intro.
apply Nat_Ind.
rewrite <- add_O_R_Identity.
rewrite add_O.
reflexivity.


intros m H.
rewrite add_S.
rewrite add_S_R.
rewrite H.
reflexivity.
Qed.

(* Now we define multiplication, 
again from equational axioms instead of derive them *)

Variable Mul : N -> N -> N.
Infix "*" := Mul.


(* Again, this are theorems of HOL, defined here as axioms *)

Axiom mul_O : forall n:N, O * n = O.
Axiom mul_S : forall m n:N, (S m) * n = n + (m * n).


(* lemmas for the symmetry of the definition on the right *)

Lemma mul_O_R_Identity : forall n:N, O = n * O.
Proof.
apply Nat_Ind.
rewrite (mul_O O).
trivial.
intros.
rewrite mul_S.
rewrite <- H.
rewrite (add_O O).
reflexivity.
Qed.




Lemma mul_S_R : forall n m : N, m * S n = m + (m * n).
Proof.
intro.
apply Nat_Ind.
rewrite (mul_O).
rewrite add_O.
rewrite (mul_O).
trivial.
intros m H.

rewrite mul_S.
rewrite H.

rewrite mul_S.
rewrite add_S.
rewrite add_S.
rewrite <- add_assoc.
rewrite <- add_assoc.
rewrite (add_conm n).
reflexivity.
Qed.


(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)
(********************************** Ex 30 ************************************)
(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)


(* We are ready for distibutivity*)


Theorem mul_add_Distr : forall n m k:N, n * (m + k) = n * m + n * k.
Proof.
intros n m.
apply Nat_Ind.
rewrite <- mul_O_R_Identity.
rewrite <- add_O_R_Identity.
rewrite <- add_O_R_Identity.
reflexivity.

intros k H.
rewrite add_S_R.
rewrite mul_S_R.
rewrite mul_S_R.
rewrite H.
rewrite <- add_assoc.
rewrite (add_conm n).
rewrite add_assoc.
reflexivity.
Qed.

Theorem mul_Assoc : forall n m k:N, n * m * k = n * (m * k).
Proof.
intros n m.
apply Nat_Ind.
rewrite <- (mul_O_R_Identity (n * m)).
rewrite <- (mul_O_R_Identity m).
rewrite <- (mul_O_R_Identity n).
reflexivity.


intros k H.
rewrite mul_S_R.
rewrite mul_S_R.
rewrite mul_add_Distr.
rewrite H.
reflexivity.
Qed.


(* conmutativity of Multiplication *)

Theorem mul_conm : forall n m:N, n * m = m * n.
Proof.
intro n.
apply Nat_Ind.
rewrite <- mul_O_R_Identity.
rewrite mul_O.
reflexivity.

intros m H.
rewrite mul_S_R.
rewrite mul_S.
rewrite H.
reflexivity.
Qed.




(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)
(********************************** Ex 31 ************************************)
(*****************************************************************************)
(*****************************************************************************)
(*****************************************************************************)



(* Definition of order *) 
Definition Leq n m := exists k : N, n + k = m.
Infix "≤" := Leq (at level 50).


(* First we prove that Leq is an order relation *)
(* We must prove reflexivity, antisymmetry, and transitivity *)

Theorem leq_Refl : forall n : N, n ≤ n.
Proof.
  intro n.  
  unfold Leq.
  exists O.
  rewrite <- add_O_R_Identity.
  reflexivity.
Qed.

Theorem leq_Trans: forall m n k:N, m ≤ n -> n ≤ k -> m ≤ k.
Proof.
  intros m n k.
  intros H H2.
  unfold Leq in H, H2.
  elim H;elim H2.
  intros k₁ H' k₂ H2'.
  unfold Leq.
  exists (k₁ + k₂).
  rewrite (add_conm k₁).
  rewrite <- add_assoc.
  rewrite H2'.
  assumption.
Qed.

(*
Axiom nat_inv: forall m n , S m = S n -> m = n.
 *) 
Lemma sum_inj : forall n k m, m+n = m+k -> n = k.
Proof.
  intros n k.
  apply (Nat_Ind (fun m => m + n = m + k -> n = k)).
  intro H.
  rewrite add_O in H; rewrite add_O in H; assumption.

  intros m H H2.
  rewrite add_S in H2.
  rewrite add_S in H2.
  apply H.
  apply S_inj_2.
  assumption.
Qed.

Lemma sum_OOO : forall m n, m+n = O -> n = O.
Proof.
  intros m.
  apply (Nat_Ind (fun n => m+n = O -> n = O)).
  intros; reflexivity.

  intros n H H1.
  rewrite add_S_R in H1.
  cut False. intro bot; elim bot.
  apply (O_not_S (m+n)).
  symmetry;assumption.
Qed.


Theorem leq_AntiSym : forall m n,  m ≤ n -> n ≤ m -> n = m.
Proof.
  intros m n L1 L2.
  unfold Leq in L1; unfold Leq in L2.
  elim L1.
  elim L2.

  intros k H s H2.
  rewrite <- H2 in H.
  rewrite add_assoc in H.
  generalize add_O_R_Identity.
  intro H3.
  rewrite H3 in H.
  apply sum_inj in H.
  cut (k = O).
  intro HK.
  rewrite HK in H.
  rewrite <- add_O_R_Identity in H.
  rewrite H in H2.
  rewrite <- add_O_R_Identity in H2.
  symmetry.
  assumption.

  apply (sum_OOO s k).
  assumption.
  
Qed.


(* The second theorem to prove in the exercise *)
Theorem leq_O : forall n:N, O ≤ n.
Proof.
  unfold Leq. intro n.
  exists n.
  rewrite add_O.
  reflexivity.
Qed.

(* The third one *)
Theorem not_S_below_O: forall n : N, ~ (S n ≤ O).
Proof.
  intro n.
  unfold not.
  unfold Leq.
  intro.
  elim H.
  intro k.
  intro H2.
  rewrite add_S in H2.
  apply (O_not_S (n+k)).
  symmetry.
  assumption.
Qed.



(* another theorem for the exercise*)
Theorem leq_S : forall n m :N, n ≤ m -> (S n) ≤ (S m).
Proof.
  unfold Leq.
  intros n m H.
  elim H. intros k H2. 
  exists k.
  rewrite add_S; rewrite H2; reflexivity.
Qed.  





(* Stronger one *)
Theorem Leq_Stable_By_S : forall m n : N, m ≤ n <-> S m ≤ S n.
Proof.
  intros m n.
  unfold iff.
  split.
  intro H.
  apply leq_S.
  assumption.
  intro H.
  unfold Leq in H.
  unfold Leq.
  elim H.
  intros k H2.
  rewrite add_S in H2.
  exists k.
  apply (S_inj_2 (m+k)).
  assumption.
Qed.


(*addition increasing*)

Theorem leq_Add_Incr :
  forall m m' n n' : N, m ≤ n -> m' ≤ n' -> m + m' ≤ (n + n').
Proof.
  intros m m' n n'.
  intros H H2.
  unfold Leq in H.
  unfold Leq in H2.
  unfold Leq.
  elim H.
  elim H2.
  intro k₁.
  intro H'.
  intro k₂.
  intro H2'.
  exists (k₁ + k₂).
  rewrite add_assoc.
  rewrite <- add_conm.
  rewrite <- add_assoc.
  rewrite H'.
  rewrite add_assoc.
  rewrite (add_conm k₂).
  rewrite H2'.
  rewrite add_conm.
  reflexivity.
Qed.



End Arith.
