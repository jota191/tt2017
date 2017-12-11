Variable P:Prop.

Theorem bottom : (P <-> ~P) -> False.
Proof.
  intro H.
  destruct H as [D R].
  absurd (P).
  intros HP.
  exact (D HP HP).
  cut (~P).
  intro HNP.
  exact (R HNP).
  intros HP.
  exact (D HP HP).
Qed.