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

Axiom Nat_Ind: 
forall P: N -> Prop, P O -> (forall n:N, P n -> P(S n)) -> forall n:N, P n.

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

Lemma add_assoc : forall m n k: N, ((n + m) + k =  n + (m + k)).
Proof.
intro m.
intro n.
apply Nat_Ind.
rewrite <- add_O_R_Identity.
rewrite <- add_O_R_Identity.
reflexivity.

intro k.
intros.
rewrite add_S_R.
rewrite add_S_R.
rewrite add_S_R.
rewrite H.
reflexivity.
Qed.

Theorem add_conm : forall n m: N, (n+m) = (m + n).
Proof.
intro.
apply Nat_Ind.
rewrite <- add_O_R_Identity.
rewrite add_O.
reflexivity.

intro m.
intros.
rewrite add_S.
rewrite add_S_R.
rewrite H.
reflexivity.
Qed.

(* Now we define product, again from equational axioms instead of derive them *)

Variable Mul : N -> N -> N.
Infix "*" := Mul.


Axiom mul_O : forall n:N, O * n = O.
Axiom mul_S : forall m n:N, (S m) * n = n + (m * n).



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
intro m.
intros.

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


Theorem mul_add_Distr : forall n m k:N, n * (m + k) = n * m + n * k.
Proof.
intros n m.
apply Nat_Ind.
rewrite <- mul_O_R_Identity.
rewrite <- add_O_R_Identity.
rewrite <- add_O_R_Identity.
reflexivity.

intro k.
intros.
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

intro k.
intros.
rewrite mul_S_R.
rewrite mul_S_R.
rewrite mul_add_Distr.
rewrite H.
reflexivity.
Qed.




Theorem mul_conm : forall n m:N, n * m = m * n.
Proof.
intro n.
apply Nat_Ind.
rewrite <- mul_O_R_Identity.
rewrite mul_O.
reflexivity.

intro m.
intros.
rewrite mul_S_R.
rewrite mul_S.
rewrite H.
reflexivity.
Qed.


(* exo 31 *)
(*TODO: explain, here or in the tex file, how can we define this order *)



(* I'll use the Prop type here*)

(*Variable Leq : N -> N -> Prop.*)

Definition Leq n m := exists k : N, n + k = m.


Infix "≤" := Leq (at level 50).


Axiom leq_O : forall n:N, O ≤ n.
Axiom leq_S : forall n m :N, n ≤ m -> (S n) ≤ (S m).

Theorem O_bottom : forall n : N, O ≤ n.
Proof.
  intro n.
  apply Nat_Ind.
    apply leq_O.

    intros m H.
    apply leq_O.
Qed.


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

(*TODO: ver si vale la pena probar esto o lo asumo*)
Axiom S_inj_2 : forall m n : N, S m = S n -> m = n.

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


(* Leq order relation*)
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



Definition Inclusion (X: nat -> Prop) (Y : nat -> Prop) := forall x:nat, X x -> Y x.

Infix "⊂" := Inclusion (at level 50).


Definition Fix F := fun x => forall X, (F X ⊂ X) -> X x. 

Definition I F := forall X Y, (X ⊂ Y) -> (F X ⊂ F Y) : Prop.

Definition Eq X Y := X ⊂ Y /\ Y ⊂ X.

Infix "≡" := Eq (at level 40).



Axiom l1 : forall F, I F
                     -> F (F (Fix F)) ⊂ F (Fix F) -> Fix F ⊂ F(Fix F).


Lemma phi_ff : forall F, I F
                         -> forall φ : nat -> Prop, F φ ⊂ φ -> Fix F ⊂ φ.
Proof.
  intros F HIF φ Hφ.
  unfold Inclusion.
  intro n.
  unfold Fix.
compute.
intros.
apply H.
intros.
unfold Inclusion in Hφ.
apply Hφ.
assumption.
Qed.



Lemma inc_trans : forall X Y Z, X ⊂ Y -> Y ⊂ Z -> X ⊂ Z.
Proof.
  intros X Y Z.
  unfold Inclusion.
  intros.
  apply (H0 x (H x H1)).
Qed.  

Lemma lemma1 : forall F, I F
                         -> forall φ : nat -> Prop, F φ ⊂ φ -> F (Fix F) ⊂ φ.
  intros F HIF φ.
  intro Hφ.
  cut (Fix F ⊂ φ).
  Focus 2.
  unfold Inclusion.
  unfold Fix.
  intros.
  apply (H φ Hφ).

  intros.
  cut (F (Fix F) ⊂ F φ).
  intros.
  apply (inc_trans (F (Fix F)) (F φ) φ).
  assumption.
  assumption.
  cut(Fix F  ⊂ φ).
  apply HIF.
  unfold Inclusion.
  unfold Fix.
  intros.
  apply (H0 φ).
  assumption.
Qed.

Lemma lemma3
  : forall F A, I F -> (forall φ, F φ ⊂ φ ->  A ⊂ φ) -> A ⊂ Fix F.
Proof.
  intros.
  unfold Inclusion.
  intros.
  unfold Fix.
  intros.
  apply H0.
  assumption.
  assumption.
Qed.

Theorem tarsky_T1 : forall F, I F -> F (Fix F) ⊂ Fix F.
Proof.
  intros F HIF.  
  apply lemma3.
  assumption.
  intros.
  apply lemma1.
  assumption.
  assumption.
Qed.  
    
Lemma tarsky_T2 : forall F, I F -> ((Fix F) ⊂ (F (Fix F))).
Proof.
  intros F HIF.
  apply l1.
  assumption.
  apply HIF.
  apply tarsky_T1.
  assumption.
Qed.



Theorem tarsky_fixpoint : forall F, I F -> F (Fix F) ≡ Fix F.
Proof.
  intros F HIF.
  unfold Eq.
  split.
  apply tarsky_T1.
  assumption.
  apply tarsky_T2.
  assumption.
Qed.

