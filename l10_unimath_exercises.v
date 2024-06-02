Require Export UniMath.Foundations.All.
Require Export UniMath.CategoryTheory.All.

(* Exercise 1 *)

(* Show that the propositional truncation of the booleans is the unit type. *)

(* Hint: use `funextsec`. *)

Definition prop_trunc (X : UU) : UU := ∏ P : hProp, ((X -> P) -> P).

Theorem ex_1 : prop_trunc bool ≃ unit.
Proof.
  set (f := fun _ : prop_trunc bool => tt).
  use tpair.
  - exact f.
  - set (g := fun _ : unit => λ P : hProp, λ trunc : bool → P, trunc true).
    apply (isweq_iso f g).
    + intro t.
      apply funextsec.
      intro P.
      apply funextsec.
      intro b.
      unfold g.
      apply (pr2 P).
    + intro t.
      unfold f.
      induction t.
      reflexivity.
Qed.

(* Exercise 2 *)

(* Define the `singleton' univalent category:
   the category with one object and no nonidentity arrows.
*)

(* I.e., define a term of `univalent_category`, defined in the library.*)

(* Hint: exercises 2 and 3 are very similar.
   Think about lemmas to use so that you don't
   have to duplicate your work.
*)

(* Old Lemmas *)

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

Lemma unit_isaprop : isaprop unit.
Proof.
  apply invproofirrelevance.
  unfold isProofIrrelevant.
  intros x y.
  induction x.
  induction y.
  reflexivity.
Defined.

Lemma isaprop_pi : ∏ X : UU, ∏ Y : X → UU, (∏ x : X, isaprop (Y x))→ isaprop (∏ x : X, Y x).
Proof.
  intros X Y pred.
  apply invproofirrelevance.
  intros f g.
  apply funextsec.
  intro x.
  apply (pred x).
Defined.

Print univalent_category.
Print category.
Print precategory.
Print is_precategory.
Print precategory_data.
Print precategory_ob_mor.

Definition trivial_mor_ob_mor (A : UU) : precategory_ob_mor.
Proof.
  use tpair.
  - exact A.
  - simpl.
    intros _ _.
    exact unit.
Defined.

Definition trivial_mor_precategory_data (A : UU) : precategory_data.
Proof.
  unfold precategory_data.
  use tpair.
  - exact (trivial_mor_ob_mor A).
  - simpl.
    unfold precategory_id_comp.
    split.
    + intro c.
      simpl.
      exact tt.
    + intros a b c f g.
      simpl.
      exact tt.
Defined.

Definition trivial_mor_is_precategory (A : UU) : is_precategory (trivial_mor_precategory_data A).
Proof.
  unfold is_precategory.
  split.
  - split.
    + intros a b f.
      apply unit_isaprop.
    + intros a b f.
      apply unit_isaprop.
  - split.
    + intros a b c d f g h.
      apply unit_isaprop.
    + intros a b c d f g h.
      apply unit_isaprop.
Defined.

Definition trivial_mor_precategory (A : UU) : precategory.
Proof.
  unfold precategory.
  use tpair.
  - exact (trivial_mor_precategory_data A).
  - exact (trivial_mor_is_precategory A).
Defined.

Definition trivial_mor_category (A : UU) : category.
Proof.
  unfold category.
  use tpair.
  - exact (trivial_mor_precategory A).
  - simpl.
    unfold has_homsets.
    intros a b.
    unfold trivial_mor_ob_mor.
    simpl.
    apply (raise_hlevel (n := 1) unit).
    exact (unit_isaprop).
Defined.

Definition singleton : univalent_category.
Proof.
  use tpair.
  - exact (trivial_mor_category unit).
  - simpl.
    unfold is_univalent.
    intros a b.
    induction a.
    induction b.
    Check idtoiso.
    Check z_iso.
    set (g := fun _ : z_iso (C := trivial_mor_category unit) tt tt => idpath tt).
    apply (isweq_iso _ g).
    + intro p.
      unfold g.
      apply (raise_hlevel (n := 0)).
      unfold isofhlevel.
      exact (unit_isaprop tt tt).
    + intro iso.
      unfold g.
      simpl.
      clear g.
      unfold identity_z_iso.
      unfold z_iso in *.
      Check is_z_isomorphism.
      Check isaset_z_iso.
      Check isaprop_is_z_isomorphism.
      Check subtypeInjectivity.
      apply subtypeInjectivity.
      * unfold isPredicate.
        intro f.
        exact (isaprop_is_z_isomorphism (C := trivial_mor_category unit) f).
      * induction iso as [f is_iso].
        simpl.
        induction f.
        reflexivity.
Defined.

Print singleton.

(* Exercise 3 *)

(* Define the `walking isomorphism' precategory:
   that is a category whose underlying set is the
   booleans and such that true ≅ false.
*)

(* I.e., define a term of type `category`.
   Unimath uses category to mean what the HoTT
   book calls precategory.
*)

Definition walking_iso := trivial_mor_category bool : category.

(* Exercise 4 *)

(* Show that the Rezk completion of the category from exercise 3
   is the category from exercise 2.
*)

(* I.e. construct a term of type `weak_equiv C D`
   where C and D are the categories defined above.
*)

Definition weak_equiv (C D : category) : UU := ∑ H : functor C D, essentially_surjective H × fully_faithful H.

Definition F_true : functor singleton walking_iso.
Proof.
  unfold functor.
  use tpair.
  - unfold functor_data.
    use tpair.
    + intro t.
      unfold walking_iso.
      simpl.
      exact true.
    + simpl.
      intros.
      exact tt.
  - simpl.
    unfold is_functor.
    split.
    + unfold functor_idax.
      simpl.
      intro.
      reflexivity.
    + unfold functor_compax.
      simpl.
      intros.
      reflexivity.
Defined.

Lemma F_true_is_es : essentially_surjective F_true.
Proof.
  unfold essentially_surjective.
  intro b.
  induction b.
  - simpl.
    unfold ishinh_UU.
    intro P.
    intro iso.
    apply iso.
    use tpair.
    + exact tt.
    + simpl.
      exact (identity_z_iso (C := walking_iso) true).
  - simpl.
    unfold ishinh_UU.
    intro P.
    intro iso.
    apply iso.
    use tpair.
    + exact tt.
    + simpl.
      unfold z_iso.
      use tpair.
      * simpl.
        exact tt.
      * simpl.
        unfold is_z_isomorphism.
        use tpair.
        ** exact tt.
        ** simpl.
           unfold is_inverse_in_precat.
           split.
           *** reflexivity.
           *** reflexivity.
Defined.

Check full.
Lemma F_true_is_full : full F_true.
Proof.
  unfold full.
  intros s t.
  unfold issurjective.
  intro b.
  simpl.
  unfold ishinh_UU.
  intro P.
  intro triv_fib.
  apply triv_fib.
  unfold hfiber.
  use tpair.
  - exact tt.
  - simpl.
    induction b.
    reflexivity.
Defined.

Check faithful.
Lemma F_true_faithful : faithful F_true.
Proof.
  unfold faithful.
  intros s t.
  unfold isincl.
  simpl.
  Compute (isofhlevelf 1 (λ _ : unit, tt)).
  intros x p1 p2.
  unfold hfiber in *.
  simpl.
  assert (isaprop : isaprop (∑ _ : unit, tt = x)).
  {
    apply invproofirrelevance.
    intros q1 q2.
    apply subtypeInjectivity.
    - unfold isPredicate.
      intro y.
      apply (raise_hlevel (n := 0)).
      exact (unit_isaprop tt x).
    - apply unit_isaprop.
  }
  use tpair.
  - apply (isaprop p1 p2).
  - simpl.
    intro p.
    apply (raise_hlevel (n := 1)).
    exact isaprop.
Defined.

Theorem singleton_is_rezk_compl_of_walking_iso : weak_equiv singleton walking_iso.
Proof.
  unfold weak_equiv.
  use tpair.
  - exact F_true.
  - split.
    + exact F_true_is_es.
    + unfold fully_faithful.
      intros a b.
      simpl.
      set (f := fun _ : unit => tt).
      set (g := fun _ : unit => tt).
      apply (isweq_iso f g).
      * intro t.
        induction t.
        reflexivity.
      * intro t.
        induction t.
        reflexivity.
Defined.