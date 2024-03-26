Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* Formulate the following statements from Rijke in
   type theory (you do not have to prove them). The
   answer to the first one (a) is given as an example. *)

(* 1a. Theorem 9.3.4 *)

Definition Eq_Σ {A : UU} {B : A → UU}: (∑ x : A, B x) → (∑ x : A, B x) → UU.
Proof.
  intros s t.
  set (s1 := pr1 s).
  set (s2 := pr2 s).
  set (t1 := pr1 t).
  set (t2 := pr2 t).
  Print transportf.
  exact (∑ p : s1 = t1, transportf B p s2 = t2).
Defined.

Definition pair_eq {A : UU} {B : A → UU} (s t : ∑ x : A, B(x)) : (s = t) → Eq_Σ s t.
Proof.
  Admitted.

Theorem Thm_9_3_4 {A : UU} {B : A → UU} (s t : ∑ x : A, B(x)) : isweq (pair_eq s t).
Proof.
  Admitted.

(* 1b. Exercise 9.2a *)

Definition const_bool (b : bool) := (λ _ : bool, b) : bool → bool.

Lemma const_is_not_eq (b : bool) : isweq (const_bool b) → empty.
Proof.
  Admitted.

(* 1c. Exercise 9.4a *)

Definition identity {X : UU} : X → X.
Proof.
  intro x.
  exact x.
Defined.

Definition has_section {X Y : UU} (f : X → Y) := ∑ (s : Y → X), f ∘ s = identity.

Definition comm_triangle {A B C : UU} (f : A → C) (g : B → C) (h : A → B) := f ~ g ∘ h.

(*
  A -h-> B
  |    /
  f  g
  v /
  C
*)
Lemma lem94a {A B X : UU} {f : A → X} {g : B → X} {h : A → B}
  (H : comm_triangle f g h) (s : has_section h) :
  (comm_triangle g f (pr1 s)) × (has_section f <-> has_section g).
Proof.
  Admitted.

(* 1d. Exercise 9.9a *)

Definition apply_rec {X : UU} (k : nat) (f : X → X) : X → X.
Proof.
  intro x.
  induction k as [| _ r].
  - exact x.
  - exact (f r).
Defined.

Definition is_finitely_cyclic {X : UU} (f : X → X) := ∏ x y : X, (∑ k : nat, (apply_rec k f) x = y).

Lemma lem99a {X : UU} (f : X → X) : (is_finitely_cyclic f) → isweq f.
Proof.
  Admitted.

(**************************************************************)

(* For the following exercises you can use the following results
  from previous exercise sessions without proofs.
  You can also use `isweq_iso` and `funextsec` from the library.
*)

Theorem hlevel_cumulative  {n : nat} {T : UU} (h : isofhlevel n T) : isofhlevel (S n) T.
Proof.
  Admitted.

Lemma contr_to_path {C : UU} (h : iscontr C) (x y : C) : x = y.
Proof.
  Admitted.

(* From here on, all `Admitted.`s should be filled in with proofs. As always, don't
  change the statements of any Theorems below, but you can always prove extra Lemmas to help.
*)

(* From the previous exercises we will need the following: *)

Theorem hlevelprop (n : nat) (A : UU) : isaprop (isofhlevel n A).
Proof.
  Admitted.

(* Exercise 2 *)

(* Show that the definitions of proposition are equivalent. *)

Lemma prop_eq {P : UU} : (isaprop P) → (∏ x y : P, x = y).
Proof.
  intro pProp.
  intros x y.
  exact (pr1 (pProp x y)).
Defined.

Lemma lem {P : UU} : (∏ x y : P, x = y) → P → isofhlevel 0 P.
Proof.
  intros H x.
  use tpair.
  - exact x.
  - intro y.
    apply H.
Defined.

Lemma prop_eq_inv {P : UU} : (∏ x y : P, x = y) → (isaprop P).
Proof.
  intro H.
  intros x y.
  use tpair.
  - apply H.
  - intro p.
    apply contr_to_path.
    set (Pcontr := lem H x).
    set (Pprop := hlevel_cumulative Pcontr).
    apply Pprop.
Defined.

Theorem prop_thm {P : UU} : (isaprop P) ≃ (∏ x y : P, x = y).
Proof.
  apply (weq_iso prop_eq prop_eq_inv).
  - intro Pisaprop.
    apply (hlevelprop 1).
  - intro H.
    apply funextsec.
    intro x.
    apply funextsec.
    intro y.
    set (Pprop := prop_eq_inv H).
    set (Pset := hlevel_cumulative Pprop).
    apply Pset.
Defined.

(* Exercise 3 *)

(* Proposition 12.1.4 from Rijke: An equivalence between propositions is
  (logically equivalent to) a logical equivalence.
*)

Theorem Prop_12_1_4 (P Q : hProp) : (P ≃ Q) <-> (P <-> Q).
Proof.
  split.
  - intro eq.
    set (f := pr1 eq).
    split.
    exact f.
    intro q.
    set (contrF := pr2 eq q).
    exact (pr1 (pr1 contrF)).
  - intro leq.
    set (f := pr1 leq).
    set (g := pr2 leq).
    use tpair.
    + exact f.
    + simpl.
    apply (isweq_iso f g).
    intro x.
    apply (pr2 P).
    intro y.
    apply (pr2 Q).
Defined.

(* Exercise 4 *)

(* Show that the dependent product type former commutes with `isaprop`.*)

Theorem prop_commutes_Π {A : UU} {B : A → UU} (p : ∏ x : A, isaprop (B x)) : isaprop (∏ x : A, (B x)).
Proof.
  apply prop_thm.
  intro f.
  intro f'.
  apply funextsec.
  intro x.
  apply p.
Defined.

(* Exercise 5 *)

(* Show that isweq f (is-contr f in Rijke) is a proposition. *)

Theorem isweq_is_prop {A B : UU} (f : A → B) : isaprop (isweq f).
Proof.
  apply prop_thm.
  unfold isweq.
  intros s t.
  apply funextsec.
  intro b.
  apply (hlevelprop 0).
Qed.


(* Exercise 6 *)

(* An equivalence between propositions is (equivalent to) a logical
   equivalence.
*)

Lemma equiv_of_prop_is_prop {P Q : hProp} : isaprop (P ≃ Q).
Proof.
  apply prop_thm.
  intros eq1 eq2.
  apply Thm_9_3_4.
  unfold Eq_Σ.
  use tpair.
  - apply prop_commutes_Π.
    intro.
    exact (pr2 Q).
  - simpl.
    apply isweq_is_prop.
Qed.

Lemma prod_eq {A B : UU} (a1 a2 : A) (b1 b2 : B) :
  (a1 = a2) → (b1 = b2) → (a1,,b1) = (a2,,b2).
Proof.
  intros p1 p2.
  induction p1.
  induction p2.
  reflexivity.
Defined.

Lemma lequiv_of_prop_is_prop {P Q : hProp} : isaprop (P <-> Q).
Proof.
  apply prop_thm.
  intros leq1 leq2.
  apply prod_eq.
  - apply prop_commutes_Π.
    intro p.
    apply (pr2 Q).
  - apply prop_commutes_Π.
    intro q.
    apply (pr2 P).
Qed.

Theorem equiv_of_prop {P Q : hProp} : (P ≃ Q) ≃ (P <-> Q).
Proof.
  set (f := pr1 (Prop_12_1_4 P Q)).
  set (g := pr2 (Prop_12_1_4 P Q)).
  apply (weq_iso f g).
  - intro eq.
    apply equiv_of_prop_is_prop.
  - intro leq.
    apply lequiv_of_prop_is_prop.
Defined.
