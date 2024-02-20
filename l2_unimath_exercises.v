Require Export UniMath.Foundations.All.

(* Exercise 1*)

(*bool is defined as the following in UniMath.Foundations.Preamble:

Inductive bool : UU :=
  | true : bool
  | false : bool.

*)

Definition not : bool → bool.
Proof.
  intro b.
  induction b.
  - exact false.
  - exact true.
Defined.

Compute (not true).
Compute (not false).

Print not.
(*
 Notes:
 - bool_rect is what we call ind_bool in the lecture.
 - The argument (λ _ : bool, bool) : bool -> Type is implicit in the lecture.*)

(* Exercise 2 *)

Search (UU → UU → UU).
About coprod.

Definition distr {A B C : UU} : (A × B) ⨿ (A × C) → A × (B ⨿ C).
(* ⨿ is ~\amalg~ *)
Proof.
  intro.
  induction X.
  - induction a as [a b].
    split.
    + exact a.
    + exact (inl b).
  - induction b as [a c].
    split.
    + exact a.
    + exact (inr c).
Defined.

(* Exercise 3 *)

(* Write ∑ as ~\Sigma~ and terms as (a,,b).*)

Definition π1 {P : UU} (Q : P → UU) : (∑ (x : P), Q x) → P.
Proof.
  intro s.
  induction s as [p q].
  exact p.
Defined.

(*Exercise 4*)

Definition add : nat → nat → nat.
Proof.
    intro n.
    intro m.
    induction m.
    - exact n.
    - exact (S IHm).
Defined.

Compute (add 5 7).
Compute (add 12 21).

Print add.


(*-------------------*)

(* Exercise 5 *)

About empty.
About unit.
Print unit.
About bool.
Print bool.
Definition boolRep : bool → UU.
(* Send false to empty, the type with no constructors and true to unit,
   the type with one constructor. *)
Proof.
  intro b.
  induction b.
  exact unit.
  exact empty.
Defined.

(* Exercise 6 *)

Definition ι : bool → nat.
Proof.
  intro b.
  induction b.
  exact 1.
  exact 0.
Defined.
Print ι.

(* Exercise 7 *)

Definition mod2 : nat → bool.
Proof.
  intro n.
  induction n as [| n IH].
  - exact false.
  - exact (not IH).
Defined.

Compute (mod2 15).
(* Should be true (aka 1) *)
Compute (mod2 20).
(* Should be false (aka 0) *)

(* Exercise 8 *)

Definition mult : nat → nat → nat.
Proof.
  intro n.
  intro m.
  induction m as [| m IH ].
  - exact 0.
  - exact (add IH n).
Defined.

Compute (mult 2 3).

(* Exercise 9 *)

Definition leq : nat → nat → bool.
Proof.
  intro n.
  induction n as [| n nleq ].
  - intro.
    exact true.
  - intro m.
    induction m as [| m _ ].
    exact false.
    exact (nleq m).
Defined.

Compute (leq 0 0).
Compute (leq 0 1).
Compute (leq 1 0).
Compute (leq 1 1).
Compute (leq 1 2).
Compute (leq 2 1).
Compute (leq 2 3).
Compute (leq 3 2).
      
(* Exercise 10 *)

About boolRep.
Print boolRep.
Search (∏ X : UU, ∏ Y : X → UU, ∏ x y : X, x = y → Y x → Y y).
Theorem leqrefl : ∏ (n : nat) , boolRep (leq n n).
Proof.
  intro n.
  induction n as [| n IH ].
  exact tt.
  apply (transportf boolRep (x:=leq n n)).
  reflexivity.
  exact IH.
Qed.

(* Exercise 11 *)

(* 
Define ≤ inductively as:
Inductive leqUU : nat → nat → UU := ...
*)
Inductive leqUU : nat → nat → UU :=
| zleqn (n : nat) : leqUU 0 n
| sleqs (n : nat) (m : nat) : leqUU n m → leqUU (S n) (S m).

Theorem leqbooltotype : ∏ (n m : nat) , boolRep (leq n m) → leqUU n m.
Proof.
  intro n.
  induction n as [| n IH ].
  - intros.
    exact (zleqn m).
  - intro  m.
    intro SnleqMProp.
    induction m as [| m _ ].
    + induction SnleqMProp.
    + apply sleqs.
      apply IH.
      simpl in SnleqMProp.
      exact SnleqMProp.
Qed.











