Require Export UniMath.Foundations.All.

Theorem dmaponpaths {X : UU} {P : X → UU} (f : (∏ x : X, P x)) {x x' : X} (e : x = x') : transportf P e (f x) = f x'.
Proof.
  induction e.
  reflexivity.
Defined.

Lemma lemma1 {X : UU} {x y z : X} (p : x = y) (q : z = x) : p = ! q @ q @ p.
Proof.
  induction p.
  induction q.
  reflexivity.
Qed.

Lemma lemma2 {X : UU} {x y : X} (p : x = y) (q : x = x) :
  ! q @ q @ p = ! q @ transportf (paths x) p (q).
Proof.
  induction p.
  induction q.
  reflexivity.
Qed.

Lemma lemma3 {X : UU} {x y z : X} (p : x = y) (q r : y = z) : (q = r) → (p @ q = p @ r).
Proof.
  intro s.
  induction p.
  induction s.
  reflexivity.
Qed.

Lemma prop_is_set {P : UU} : (∏ x y : P, x = y) → (∏ x y : P, (∏ p q : x = y, p = q)).
Proof.
  intros H x y p q.
  set (h := H x).
  transitivity (! h x @ (h x @ p)).
  apply lemma1.
  transitivity (! h x @ (transportf (paths x) p (h x))).
  apply lemma2.
  transitivity ((! h x) @ (h y)).
  - apply lemma3.
    apply dmaponpaths.
  - transitivity (! h x @ (transportf (paths x) q (h x))).
    + apply lemma3.
      symmetry.
      apply dmaponpaths.
    + symmetry.
      transitivity (! h x @ h x @ q).
      * apply lemma1.
      * apply lemma2.
Qed.

Lemma prop_eq_inv {P : UU} : (∏ x y : P, x = y) → (isaprop P).
Proof.
  intro H.
  intros x y.
  use tpair.
  - apply H.
  - intro p.
    apply prop_is_set.
    exact H.
Defined.

Lemma prop_eq {P : UU} : (isaprop P) → (∏ x y : P, x = y).
Proof.
  intro pProp.
  intros x y.
  exact (pr1 (pProp x y)).
Defined.

Theorem prop_thm {P : UU} : (isaprop P) ≃ (∏ x y : P, x = y).
Proof.
  apply (weq_iso prop_eq prop_eq_inv).
  - intro Pisaprop.
    apply isapropisaprop.
  - intro H.
    apply funextsec.
    intro x.
    apply funextsec.
    intro y.
    apply prop_is_set.
    exact H.
Defined.
