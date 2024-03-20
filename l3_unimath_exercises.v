Require Export UniMath.Foundations.All.

(* Example 1*)

(* Notes:
- idpath is the name in Unimath for refl.
- Defined as maponpaths in UniMath.Foundations.PartA.*)

(*
The identity type is defined in Unimath as:

Inductive paths {A:UU} (a:A) : A -> UU := paths_refl : paths a a.
Notation "a = b" := (paths a b) : type_scope.
Notation idpath := paths_refl .
*)

Definition ap {A B : UU} (f : A → B) {x y : A} (p : x = y) : f x = f y.
Proof. 
  induction p.
  apply idpath.
Defined.

Search (∏ A B : UU , ∏ f : A → B, ∏ x y : A , x = y → f x = f y).

About maponpaths.

About ap.
(* Example 2 *)

(* Note: this might hold definitionally based on how you defined add. If so, prove add n 0 = n instead.*)

Print add.

Definition left_unit (n : nat) : add 0 n = n.
Proof.
  apply idpath.
Defined.

Definition right_unit (n : nat) : add n 0 = n.
Proof.
  induction n.
  - unfold add.
  apply idpath.
  - unfold add.
  simpl.
    apply ap.
    exact IHn.
Defined.

(* Example 3 *)

(* We make the parameter {A:UU} in paths explicit by writing @paths. *)

Definition reflexive {A : UU} (R: A → A → UU) : UU := ∏ a : A, R a a.

Lemma reflexive_paths (A : UU): reflexive (@paths A).
Proof.
  unfold reflexive.
  intro a.
  apply idpath.
Defined.

(* Example 4 *)

Definition symmetric {A : UU} (R: A → A → UU) : UU := ∏ (a b : A), R a b → R b a.

Lemma symmetric_paths (A : UU) : symmetric (@paths A).
Proof.
  unfold symmetric.
  intros a b.
  intro p.
  induction p.
  apply idpath.
Defined.

(* Example 5 *)

Definition transitive {A : UU} (R: A → A → UU) : UU := ∏ (a b c : A), a = b → b = c → a = c.

Lemma transitive_paths (A : UU) : transitive (@paths A).
Proof.
  unfold transitive.
  intros a b c p q.
  induction p.
  induction q.
  apply idpath.
Defined.

(* Example 6 *)

Definition equivalence {A : UU} (R: A → A → UU) : UU := (reflexive R) × (symmetric R) × (transitive R).

Theorem equivalence_paths (A : UU) : equivalence (@paths A).
Proof.
  exact (reflexive_paths A,,symmetric_paths A,,transitive_paths A).
Defined.

(* Example 7 *)

(* Everything respects equality. *)

(* Note: transport is defined as transportf in UniMath.Foundations.PartA.*)

Theorem transport {A : UU} {D : A → UU} {a b : A} (d : D a) (p: a = b) : D b.
Proof.
  induction p.
  exact d.
Defined.


(*********************************)

(* Exercise 8 *)

Theorem complicatedTransport {A : UU} {D : A → UU} {a b c : A} (p : a = b) (q : b = c) (d : D c) : D a.
Proof.
  induction q.
  induction p.
  exact d.
Defined.

(* Exercise 9 *)

Lemma add_S_comm : ∏ n m : nat , n + S m = S (n + m).
Proof.
  intros n m.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Theorem add_comm : ∏ n m : nat , n + m = m + n.
Proof.
  intros n m.
  induction m.
  - simpl.
    induction n.
    + reflexivity.
    + simpl.
      apply maponpaths.
      exact IHn.
  - simpl.
    rewrite (! IHm).
    apply add_S_comm.
Qed.

(* Exercise 9 *)

Theorem mul_left_id : ∏ n : nat , mul 1 n = n.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

(* Exercise 10 *)

Theorem mul_right_id : ∏ n : nat , mul n 1 = n.
Proof.
  intro n.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    transitivity (1+n).
    apply add_comm.
    simpl.
    reflexivity.
Qed.

(* Exercise 11 *)

(* Define what is means to be divisible by 2 and divisible by 4,
   and show that being divisible by 4 implies being divisible by 2. *)

Definition divisibleBy2 (n : nat) := (∑ (d : nat), 2 * d = n).

Definition divisibleBy4 (n : nat) := (∑ (d : nat), 4 * d = n).


Print add.
Theorem add_assoc : ∏ n m k : nat, n + (m + k) = n + m + k.
Proof.
  intros n m k.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

About maponpaths.
Lemma lem : ∏ n : nat, 2 * (2 * n) = 4 * n.
Proof.
  intro n.
  simpl.
  apply add_assoc.
Qed.

Theorem divBy4_implies_divBy2 : ∏ n : nat , (divisibleBy4 n → divisibleBy2 n).
Proof.
  intros n div4.
  unfold divisibleBy2.
  destruct div4 as [d p].
  set (d2 := 2 * d).
  set (p2 := (lem d) @ p).
  exact (d2,,p2).
Qed.
