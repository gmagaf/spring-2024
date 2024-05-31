Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(*
  Example 12.1.2 (second half) from Rijke:
  The empty type is a proposition.
*)
Theorem empty_isaprop : isaprop empty.
Proof.
  unfold isaprop.
  unfold isofhlevel.
  intro e1.
  induction e1.
Defined.

(* Exercise 2 *)

(*
  Example 12.1.2 (first half) from Rijke:
  Every contractible type is a proposition.
*)

Theorem iscontr_to_isaprop : ∏ A : UU, (iscontr A) → (isaprop A).
Proof.
  intros A contr.
  induction contr as [c contr].
  unfold isaprop.
  intros a b.
  use tpair.
  - exact ((contr a) @ !(contr b)).
  - intro p.
    simpl.
    induction p.
    symmetry.
    apply pathsinv0r.
Defined.

(* Exercise 3 *)

(*
  (i ⇒ iii) in Proposition 12.1.3 of Rijke:
  If a proposition is inhabited, then it is contractible.
*)
Theorem inhabited_prop_iscontr {A : UU} (prop : isaprop A) : A → (iscontr A).
Proof.
  intro a.
  use tpair.
  - exact a.
  - intro a'.
    symmetry.
    exact (pr1 (prop a a')).
Defined.

(* Exercise 4 *)

(*
   Proposition 12.4.3 of Rijke:
   If a type has h-level n, then it has h-level n+1.
*)
Theorem raise_hlevel {n : nat} : ∏ A : UU, (isofhlevel n A) → (isofhlevel (n+1) A).
Proof.
  induction n as [| n IH].
  - exact iscontr_to_isaprop.
  - intros A suc_level.
    simpl.
    intros a a'.
    apply IH.
    exact (suc_level a a').
Defined.

(* Exercise 5 *)

(* Every statement of the form ishlevel n A is a proposition.*)

(* Hint: use ~impred_iscontr~ and ~isofhleveltotal2~ from the library. *)

Lemma iscontr_prop {A : UU} : isaprop (iscontr A).
Proof.
  intros [c1 contr1] [c2 contr2].
  simpl.
  assert (h1 : ∏ x : A, iscontr (∏ t : A, t = x)).
  {
    intro x.
    apply impred_iscontr.
    intro t.
    apply (iscontr_to_isaprop A).
    exact (c1,,contr1).
  }
  assert (h2 : iscontr(∑ cntr : A, ∏ x : A, x = cntr)).
  {
    Check isofhleveltotal2.
    apply (isofhleveltotal2 0 (λ cntr : A, ∏ x : A, x = cntr) (c1,,contr1)).
    exact h1.
  }
  apply iscontr_to_isaprop.
  apply h2.
Defined.

Theorem hlevelprop (n : nat) : ∏ A : UU, isaprop (isofhlevel n A).
Proof.
  induction n as [|n IH].
  - intro A.
    exact iscontr_prop.
  - intro A.
    simpl.
    apply impred_isaprop.
    intro x.
    apply impred_isaprop.
    intro y.
    exact (IH (x = y)).
Defined.