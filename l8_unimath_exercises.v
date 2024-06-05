Require Export UniMath.Foundations.All.

(* Hint: use `isweq_iso`, `funextsec`, `total2_paths_f`,
  `isapropiscontr`, `proofirrelevance `, `isapropisweq`,
  `univalenceAxiom`, `twooutof3a`, `isapropisaset`,
  `isapropifcontr`.
*)

(* Exercise 1 *)

(* Show that equalities of subtypes are the same as the equalities
   in the super types.
*)

Theorem subtype_eq {A : UU} {p : A → UU} (pPred : ∏ a : A, isaprop (p a)) (s t : ∑ a : A, p a) :
  pr1 s = pr1 t ≃ s = t.
Proof.
  Admitted.

(* Exercise 2 *)

(* Show univalence for sets. *)

Theorem type_eq_to_set_eq {S T : hSet} : (pr1 S ≃ pr1 T) → (S ≃ T).
Proof.
  intro type_eq.
  set (f := pr1 type_eq).
  use tpair.
  - exact f.
  - exact (pr2 type_eq).
Defined.

Theorem set_eq_to_type_eq {S T : hSet} : (S ≃ T) → (pr1 S ≃ pr1 T).
Proof.
  intro eq.
  set (f := pr1 eq).
  use tpair.
  - exact f.
  - exact (pr2 eq).
Defined.

Theorem set_eq_eq_type_eq (S T : hSet) : (pr1 S ≃ pr1 T) ≃ (S ≃ T).
Proof.
  Print isweq_iso.
  use tpair.
  - exact type_eq_to_set_eq.
  - apply (isweq_iso type_eq_to_set_eq set_eq_to_type_eq).
    + intro typeEq.
      reflexivity.
    + intro setEq.
      reflexivity.
Qed.

Print hSet.
Print univalenceAxiom.
Print univalenceStatement.
Theorem underlying_ua {S T : UU} : (S = T) ≃ (S ≃ T).
Proof.
  use tpair.
  - exact eqweqmap.
  - exact (univalenceAxiom S T).
Qed.

Search (∏ A : UU, A → A).
Search (∏ A B C : UU, (A → B) → (B → C) → (A → C)).
Definition isqEquiv {S T : UU} (f : S → T) := ∑ g : T → S, g ∘ f = idfun S × f ∘ g = idfun T: UU.

Definition iso (S T : UU) := ∑ f : S → T, isqEquiv f : UU.

Lemma equiv_to_inv {S T : UU} {f : S → T} : isweq f → ∏ t : T, hfiber f t.
Proof.
  intros weq t.
  exact (pr1 (weq t)).
Defined.

Theorem equiv_leq_qequiv {S T : UU} (f : S → T) : isweq f <-> isqEquiv f.
Proof.
  split.
  - intro weq.
    unfold isqEquiv.
    set (gFib := equiv_to_inv weq).
    use tpair.
    + intro t.
      exact (pr1 (gFib t)).
    + split.
      * apply funextsec.
        intro s.
        simpl.
        unfold gFib.
        unfold equiv_to_inv.
        symmetry.
        set (p := pr2 (weq (f s)) (s,,idpath (f s))).
        apply (maponpaths pr1 p).
      * apply funextsec.
        intro t.
        simpl.
        unfold gFib.
        exact (pr2 (equiv_to_inv weq t)).
  - intro qeq.
    set (g := pr1 qeq).
    set (inv := pr2 qeq).
    apply (isweq_iso f g).
    + intro s.
      apply (maponpaths (fun h : S → S => h s) (pr1 inv)).
    + intro t.
      apply (maponpaths (fun h : T → T => h t) (pr2 inv)).
Qed.

Lemma weq_to_iso {S T : UU} : (S ≃ T) -> iso S T.
Proof.
  intro eq.
  set (f := pr1 eq).
  set (feq := pr2 eq).
  set (feq_to_iso := pr1 (equiv_leq_qequiv f)).
  exact (f,, feq_to_iso feq).
Defined.

Lemma iso_to_weq {S T : UU} : iso S T → (S ≃ T).
Proof.
  intro iso.
  set (f := pr1 iso).
  set (g := pr1 (pr2 iso)).
  set (gf_id := pr1 (pr2 (pr2 iso))).
  set (fg_id := pr2 (pr2 (pr2 iso))).
  apply (weq_iso f g).
  - intro s.
    apply (maponpaths (fun h => h s) gf_id).
  - intro t.
    apply (maponpaths (fun h => h t) fg_id).
Defined.

Lemma isaprop_fun_eq : (∏ (A B : UU), ∏ (f g : A → B), (isaprop (∏ x : A, f x = g x)) → (isaprop (f = g))).
Proof.
  intros A B f g homotProp.
  Print isweqtoforallpathsUAH.
  Check (isweqtoforallpathsUAH univalenceAxiom A (fun _ => B) f g).
  assert (hyp : (f = g) = homot f g).
  {
    apply univalenceAxiom.
    use tpair.
    - apply (toforallpaths _ f g).
    - exact (isweqtoforallpathsUAH univalenceAxiom A (fun _ => B) f g).
  }
  apply (transportf isaprop (!hyp)).
  exact homotProp.
Qed.

Theorem prop_commutes_Π {A : UU} {B : A → UU} (p : ∏ x : A, isaprop (B x)) : isaprop (∏ x : A, (B x)).
Proof.
  (* Prooven in hw2 ex *)
  Admitted.

Lemma isaprop_g {S T : UU} (SH : isaset S) (TH : isaset T) {f : S → T} {g : T → S} : isaprop (g ∘ f = idfun S × f ∘ g = idfun T).
Proof.
  Search (∏ (A B : UU), (isaprop A) → (isaprop B) → (isaprop (A × B))).
  apply isapropdirprod.
  - apply isaprop_fun_eq.
    apply prop_commutes_Π.
    intro s.
    apply SH.
  - apply isaprop_fun_eq.
    apply prop_commutes_Π.
    intro t.
    apply TH.
Qed.

Lemma isaprop_qequiv {S T : UU} (SH : isaset S) (TH : isaset T) (f : S → T) : isaprop (isqEquiv f).
Proof.
  Search (∏ X : UU, isProofIrrelevant X → isaprop X).
  apply invproofirrelevance.
  intros e1 e2.
  set (g1 := pr1 e1).
  set (g2 := pr1 e2).
  assert (g1 = g2) as p.
  {
    apply funextsec.
    intro t.
    transitivity (g1 (f (g2 t))).
    - symmetry.
      apply (maponpaths g1).
      apply (maponpaths (fun h : T → T => h t) (pr2 (pr2 e2))).
    - apply (maponpaths (fun h : S → S => h (g2 t)) (pr1 (pr2 e1))).
  }
  Print total2_paths_f.
  apply (total2_paths_f p).
  apply (isaprop_g SH TH).
Qed.

Lemma set_iso_is_equiv (S T : UU) (SH : isaset S) (TH : isaset T) : isweq (iso_to_weq (S := S) (T := T)).
Proof.
  apply (isweq_iso iso_to_weq weq_to_iso).
  - intro iso.
    unfold iso_to_weq.
    unfold weq_to_iso.
    simpl.
    apply subtype_eq.
    + intro f.
      apply (isaprop_qequiv SH TH).
    + reflexivity.
  - intro eq.
    unfold weq_to_iso.
    unfold iso_to_weq.
    simpl.
    apply subtype_eq.
    + intro f.
      apply (isapropisweq).
    + reflexivity.
Qed.

Theorem type_eq_eq_set_iso (S T : UU) (SH : isaset S) (TH : isaset T) : (iso S T) ≃ (S ≃ T).
Proof.
  use tpair.
  - exact iso_to_weq.
  - apply (set_iso_is_equiv S T SH TH).
Qed.

Theorem sets_is_univalent (S T : UU) (SH : isaset S) (TH : isaset T) : (S = T) ≃ (iso S T).
Proof.
  Search (∏ A B C : UU, (A ≃ B) → (B ≃ C) → (A ≃ C)).
  apply (weqcomp (Y:= S ≃ T)).
  - apply underlying_ua.
  - Search (∏ A B : UU, (A ≃ B) → (B ≃ A)).
    apply invweq.
    apply (type_eq_eq_set_iso S T SH TH).
Qed.

(* Exercise 3 *)

(* Define the type of categories and univalence for categories. *)

Definition CatOb := UU.
Definition CatHom (catOb : CatOb) := catOb → catOb → hSet : UU.
Definition IdMor (catOb : CatOb) (hom : CatHom catOb) := ∏ c : catOb, hom c c.
Definition CompMor (catOb : CatOb) (hom : CatHom catOb) :=
  ∏ a b c : catOb, hom a b → hom b c → hom a c.
Definition UnitLawR (ob : CatOb) (hom : CatHom ob) (id : IdMor ob hom) (comp : CompMor ob hom) :=
  ∏ a b : ob, ∏ f : hom a b, comp a b b f (id b) = f.
Definition UnitLawL (ob : CatOb) (hom : CatHom ob) (id : IdMor ob hom) (comp : CompMor ob hom) :=
  ∏ a b : ob, ∏ f : hom a b, comp a a b (id a) f = f.
Definition AssocLaw (ob : CatOb) (hom : CatHom ob) (id : IdMor ob hom) (comp : CompMor ob hom) :=
  ∏ a b c d : ob, ∏ f : hom a b, ∏ g : hom b c, ∏ h : hom c d,
  comp a b d f (comp b c d g h) = comp a c d (comp a b c f g) h.
Definition pre_cat :=
  ∑ ob : CatOb,
  ∑ hom : CatHom ob,
  ∑ id : IdMor ob hom,
  ∑ comp : CompMor ob hom,
  UnitLawR ob hom id comp × UnitLawL ob hom id comp × AssocLaw ob hom id comp : UU.

Lemma ob (cat : pre_cat) : CatOb.
Proof.
  induction cat as [ob _].
  exact ob.
Defined.

Lemma hom (cat : pre_cat) (a b : (ob cat)) : hSet.
Proof.
  induction cat as [ob [hom r]].
  exact (hom a b).
Defined.


Definition is_isomor (cat : pre_cat) (a b : (ob cat)) (f : hom cat a b) : UU.
Proof.
  induction cat as [ob [hom [id [comp r]]]].
  unfold CatHom in *.
  simpl in a.
  simpl in b.
  exact (
  ∑ g : hom b a,
  comp a b a f g = id a × comp b a b g f = id b
  ).
Defined.

Definition isomor (cat : pre_cat) (a b : (ob cat)) :=
  ∑ f : hom cat a b, is_isomor cat a b f : UU.

Definition id_to_iso (cat : pre_cat) (a b : (ob cat)) :
    a = b → isomor cat a b.
Proof.
  intro p.
  induction cat as [ob [hom [id [comp laws]]]].
  induction p.
  use tpair.
  - exact (id a).
  - use tpair.
    + exact (id a).
    + split.
      * set (r := (pr1 laws)).
        unfold UnitLawR in r.
        exact (r a a (id a)).
      * set (l := (pr1 (pr2 laws))).
        unfold UnitLawL in l.
        exact (l a a (id a)).
Defined.

Print isweq.
Definition category :=
  ∑ cat : pre_cat,
  ∏ a b : (ob cat), isweq (id_to_iso cat a b) : UU.

