Require Export UniMath.Foundations.All.

Theorem prob1 (A : UU) (a b c : A) : (a = b) -> (b = c) -> (a = c).
Proof.
  intro p.
  intro q.
  induction q.
  exact p.
Qed.

Theorem prob2 (A : UU) (a : A) : iscontr (∑ x : A, a = x).
Proof.
  use tpair.
  - exact (a,,idpath a).
  - simpl.
    intro pair.
    induction pair as [a' p].
    induction p.
    exact (idpath (a,,idpath a)).
Qed.