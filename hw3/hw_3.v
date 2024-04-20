Require Export UniMath.Foundations.All.
Require Export UniMath.CategoryTheory.All.

(* Instructions:
   Do Exercises 1 and 2 here in UniMath.
   Do Exercise 3 in LaTeX.
   No exercise should be done both in UniMath and LaTeX.
   As usual, you will submit one .v file and one .pdf file.
*)

(* You can use anything proven in previous exercises or homework, and
   `impred_isaprop`, `funextsec`, `weqtopaths`,
   `isweqtoforallpathsAxiom`, `toforallpaths`,
   `isweqhomot`, `twooutof3c`,
   and anything else from UniMath.Foundations.UnivalenceAxiom.
*)

(* Exercise 1 *)

(* Define the category of sets. *)

Definition ob := hSet : UU.
Definition homset : precategory_ob_mor.
Proof.
  use tpair.
  - exact hSet.
  - intros X1 X2.
    exact (pr1 X1 → pr1 X2).
Defined.

Definition set_precategory_data : precategory_data.
Proof.
  use tpair.
  - exact homset.
  - split.
    + intro X.
      intro x.
      exact x.
    + intros X Y Z f g.
      exact (g ∘ f).
Defined.

Lemma set_is_precategory : is_precategory set_precategory_data.
Proof.
  split.
  - split.
    + intros X Y f.
      reflexivity.
    + intros X Y f.
      reflexivity.
  - split.
    + intros X Y Z W f g h.
      reflexivity.
    + intros X Y Z W f g h.
      reflexivity.
Defined.

Theorem set_category : category.
Proof.
  use tpair.
  - exact (set_precategory_data,,set_is_precategory).
  - simpl.
    unfold has_homsets.
    intros X Y.
    intros f g.
    apply (transportf isaprop (x := ∏ x : pr1 X, f x = g x)).
    + apply weqtopaths.
      apply weqfunextsec.
    + apply impred_isaprop.
      intro x.
      apply (pr2 Y).
Defined.

(* Exercise 2 *)

(* Show that the category from exercise 1 is univalent.*)

Definition setiso (S T : hSet) : UU :=
  ∑ f : S → T ,
  ∑ g : T → S ,
  g ∘ f ~ idfun S
  ×
  f ∘ g ~ idfun T.

Definition set_idtoiso (S T : hSet) : (S = T) → (setiso S T).
Proof.
  intro e.
  induction e.
  use tpair.
  - exact (idfun S).
  - use tpair.
    + exact (idfun S).
    + split.
      * intro s.
        simpl.
        apply idpath.
      * intro s.
        simpl.
        apply idpath.
Defined.

Theorem set_univalence (S T : hSet) : isweq (set_idtoiso S T).
Proof.
  Admitted.
(* You don't have to fill this proof in; it is from previous exercises.*)

(* We also use this Theorem from l8 exercises. *)
Theorem subtype_equalities (A : UU) (P : A → UU) (a b : ∑ x : A, P x) (prop : ∏ a : A , isaprop (P a)) : (pr1 a = pr1 b) ≃ (a = b).
Proof.
  Admitted.


Lemma setiso_to_z_iso (S T : set_category) : setiso S T → z_iso S T.
Proof.
  intro iso.
  set (f := pr1 iso).
  set (g := pr1 (pr2 iso)).
  unfold z_iso.
  use tpair.
  - exact f.
  - unfold is_z_isomorphism.
    use tpair.
    + exact g.
    + unfold is_inverse_in_precat.
      split.
      * apply funextsec.
        exact (pr1 (pr2 (pr2 iso))).
      * apply funextsec.
        exact (pr2 (pr2 (pr2 iso))).
Defined.

Lemma z_iso_to_setiso (S T : set_category) : z_iso S T → setiso S T.
Proof.
  intro ziso.
  set (f := pr1 ziso).
  set (g := pr1 (pr2 ziso)).
  use tpair.
  - exact f.
  - use tpair.
    + exact g.
    + split.
      * apply toforallpaths.
        exact (pr1 (pr2 (pr2 ziso))).
      * apply toforallpaths.
        exact (pr2 (pr2 (pr2 ziso))).
Defined.

Lemma prod_eq {A B : UU} (a1 a2 : A) (b1 b2 : B) :
  (a1 = a2) → (b1 = b2) → (a1,,b1) = (a2,,b2).
Proof.
  intros p1 p2.
  induction p1.
  induction p2.
  reflexivity.
Defined.

Lemma z_iso_isprop (S T : set_category) (f : set_category ⟦ S, T ⟧) : isaprop (is_z_isomorphism f).
Proof.
  apply invproofirrelevance.
  unfold is_z_isomorphism.
  intros p1 p2.
  apply subtype_equalities.
  - intro g.
    apply invproofirrelevance.
    unfold is_inverse_in_precat.
    intros q1 q2.
    apply prod_eq.
    + apply (pr2 set_category).
    + apply (pr2 set_category).
  - set (g1 := pr1 p1).
    set (g2 := pr1 p2).
    transitivity (g1 ∘ f ∘ g2).
    + apply funextfun.
      intro t.
      apply (maponpaths g1).
      set (p := !pr22 p2).
      exact (maponpaths (fun h => h t) p).
    + apply funextfun.
      intro s.
      set (p := pr12 p1).
      apply (maponpaths (fun h => h (g2 s)) p).
Qed.

Lemma setiso_isprop (S T : hSet) (f : S → T) :
  isaprop (∑ g : T → S, g ∘ f ~ idfun S × f ∘ g ~ idfun T).
Proof.
  apply invproofirrelevance.
  intros p1 p2.
  apply subtype_equalities.
  - intro g.
    apply invproofirrelevance.
    unfold is_inverse_in_precat.
    intros q1 q2.
    apply prod_eq.
    + apply funextsec.
      intro s.
      apply (pr2 S).
    + apply funextsec.
      intro t.
      apply (pr2 T).
  - set (g1 := pr1 p1).
    set (g2 := pr1 p2).
    transitivity (g1 ∘ f ∘ g2).
    + apply funextfun.
      intro t.
      symmetry.
      apply (maponpaths g1).
      apply (pr22 p2).
    + apply funextfun.
      intro t.
      apply (pr12 p1).
Qed.

Lemma comp_lemma (S T : set_category) : (setiso_to_z_iso S T) ∘ set_idtoiso S T = (λ p : S = T, idtoiso p).
Proof.
  apply funextsec.
  intro p.
  induction p.
  apply subtype_equalities.
  - exact (z_iso_isprop S S).
  - reflexivity.
Qed.

Lemma setiso_to_z_iso_isweq (S T : set_category) : isweq (setiso_to_z_iso S T).
Proof.
  apply (isweq_iso (setiso_to_z_iso S T) (z_iso_to_setiso S T)).
  - intro iso.
    apply subtype_equalities.
    + exact (setiso_isprop S T).
    + reflexivity.
  - intro z_iso.
    apply subtype_equalities.
    + exact (z_iso_isprop S T).
    + reflexivity.
Qed.

Lemma set_is_univalent : is_univalent set_category.
Proof.
  unfold is_univalent.
  intros S T.
  apply (isweqhomot (setiso_to_z_iso S T ∘ set_idtoiso S T)).
  - apply toforallpaths.
    exact (comp_lemma S T).
  - apply twooutof3c.
    + exact (set_univalence S T).
    + exact (setiso_to_z_iso_isweq S T).
Qed.

Theorem set : univalent_category.
Proof.
  exact (set_category,,set_is_univalent).
Qed.

(* Exercise 3 *)

(* Do not do this one in Unimath, only in LaTeX. *)

(* Consider the category G of groupoids, and the class D ⊆ mor (G) of isofibrations.
   Show that this is a display map category, and that it has the two additional
   properties required of a display map category. That is, show that:
  i) every X → * is a display map
  ii) D is closed under isomorphisms
  iii) D is stable under pullback
  iv) D contains all isomorphisms
  v) D is closed under composition

  Use the definition for isofibration and any results from the nLab page
  https://ncatlab.org/nlab/show/isofibration.
  Hint: use Prop 3.1.
 *)