
Definition Inclusion (X: nat -> Prop) (Y : nat -> Prop) := forall x:nat, X x -> Y x.


Infix "⊂" := Inclusion (at level 50).


Definition Fix F := fun x => forall X, (F X ⊂ X) -> X x. 

Definition I F := forall X Y, (X ⊂ Y) -> (F X ⊂ F Y) : Prop.

Definition Eq X Y := X ⊂ Y /\ Y ⊂ X.

Infix "≡" := Eq (at level 40).





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
  cut(Fix F ⊂ φ).
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

Lemma l1 : forall F, I F
                     -> F (F (Fix F)) ⊂ F (Fix F) -> Fix F ⊂ F(Fix F).
Proof.
  intros F HIF H.
  apply phi_ff.
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

