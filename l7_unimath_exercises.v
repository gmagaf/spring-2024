Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* Propositional truncation is defined slightly differently
   in UniMath than how I defined it. Show that it has the
   same properties in the next few exercises.
*)

Print univalenceStatement.
Print eqweqmap.
Variable ua : univalenceStatement.

Variable funext : funextsecStatement.

Definition prop_trunc (X : UU) : UU := ∏ P : hProp, ((X -> P) -> P).

Theorem prop_trunc_unit {X : UU} : X → prop_trunc X.
Proof.
  intro x.
  unfold prop_trunc.
  intro P.
  intro tranc.
  apply tranc.
  exact x.
Defined.

(* Exercise 2 *)

Print hProp.
Print isaprop.
Print isofhlevel.
Theorem prop_trunc_unit_eq {X : UU} {x y : X} : prop_trunc_unit x = prop_trunc_unit y.
Proof.
  unfold prop_trunc_unit.
  apply funext.
  unfold homot.
  intro P.
  apply funext.
  unfold homot.
  intro trunc.
  apply (pr2 P).
Defined.

(* Exercise 3 *)

(* Use ~invproofirrelevance~ or what you have done before.*)

Print invproofirrelevance.
Print isProofIrrelevant.
Theorem prop_trunc_prop {X : UU} : isaprop (prop_trunc X).
Proof.
  apply invproofirrelevance.
  unfold prop_trunc.
  intros tx ty.
  apply funext.
  intro P.
  apply funext.
  intro f.
  apply (pr2 P).
Qed.

(* Exercise 4 *)

(* Hint: use ~isapropimpl~ and ~isweqimplimpl~.*)

Print isapropimpl.
Print isweqimplimpl.
Theorem univ_prop_prop_trunc (T : UU) (P : hProp) : (T → P) ≃ (prop_trunc T → P).
Proof.
  set (tf := fun f : T → P => fun tx : prop_trunc T => tx P f).
  use tpair.
  - exact tf.
  - apply (isweqimplimpl tf).
    + intros truncf t.
      apply truncf.
      exact (prop_trunc_unit t).
    + apply (isapropimpl T P (pr2 P)).
    + apply (isapropimpl (prop_trunc T) P (pr2 P)).
Qed.

(* Exercise 5 *)

(* Show that hProp is a Set. *)

(* Hint: use ~weqtopaths~, ~isapropweqtoprop~, ~subtypeInjectivity~, and ~isapropisofhlevel~. *)

Print isapropweqtoprop.
Lemma isaprop_eq_of_prop {P Q : hProp} : isaprop (P ≃ Q).
Proof.
  apply isapropweqtoprop.
  exact (pr2 Q).
Qed.

Lemma equiv_to_id {A B : UU} (e : A ≃ B) : (A = B).
Proof.
  apply ua.
  exact e.
Qed.

Lemma ua_eq (A B : UU) : (A = B) = (A ≃ B).
Proof.
  apply equiv_to_id.
  exact (eqweqmap,,ua A B).
Qed.

Theorem hProp_is_Set : isaset hProp.
Proof.
  intros P Q.
  induction P as [P p].
  induction Q as [Q q].
  Print subtypeInjectivity.
  set (a := subtypeInjectivity isaprop (isapropisofhlevel 1) (P,,p) (Q,,q)).
  set (b := equiv_to_id a).
  simpl in b.
  Print transportf.
  apply (transportf isaprop (!b)).
  apply (transportf isaprop (!(ua_eq P Q))).
  apply isapropweqtoprop.
  exact q.
Qed.
