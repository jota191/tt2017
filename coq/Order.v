(* TODO : put here exo 31 and manage modules*)
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
