Parameter N : Type.

Parameter O : N.
Parameter S : N -> N.

Axiom succ_inj: forall n m :N, n <> m -> S m <> S n.
Axiom Oisnotsucc: forall n :N, O <> S n.

Parameter Add : N -> N -> N.

Notation "x +++ y" := (Add x y) (at level 70).

Axiom add_O : forall x y : N, (S x)+++ y = S (x +++ y).
Axiom add_S : forall x y : N, O +++ y = y.


Axiom Nat_ind: 
forall P: N -> Prop, P O -> (forall n:N, P n -> P(S n)) -> forall n:N, P n.

Theorem nat_conm : forall n m: N, (n+++m) = (m +++ n).
intro.
apply Nat_ind.








