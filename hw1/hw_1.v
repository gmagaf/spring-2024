Require Export UniMath.Foundations.All.

(* Exercise 1 *)

Theorem comp_app { P Q R : UU } (f : P → Q) (g : Q → R) (p : P) : R.
Proof.
  apply g.
  apply f.
  exact p.
Qed.

(* Exercise 2 *)

Theorem curried_proj {P Q R : UU} : (P → (Q × R)) → (P → Q).
Proof.
  intros pToQR p.
  induction (pToQR p) as [q _].
  exact q.
Qed.

(* Exercise 3 *)

Theorem exp : nat → nat → nat.
Proof.
  intros base e.
  induction e as [| _ IH].
  exact 1.
  exact (IH * base).
Defined.


Compute (exp 5 1).
(* Should output 5. *)

Compute (exp 3 2).
(* Should output 9. *)

(* Exercise 4 *)

Search (∏ X Y : UU, ∏ f : X → Y, ∏ x y : X, x = y → (f x) = (f y)).
(*
maponpaths:
  ∏ {T1 T2 : UU} (f : T1 → T2) {t1 t2 : T1},
  t1 = t2 → f t1 = f t2
*)

(* This command searches the library for functions of this type. You should see in the output that ~maponpaths~ is of this type. You can then print ~maponpaths~ (i.e. write "Print maponpaths.") to see the definition.

You can use this to find other lemmas from the library. You can use any facts without proof from the library about addition and multiplication as well as ~maponpaths~.*)

Search (forall m : nat, m * 1 = m).
(* natmultr1: ∏ n : nat, n * 1 = n *)
Search (forall n m : nat, n * m = m * n).
(* natmultcomm: ∏ n m : nat, n * m = m * n *)
Search (forall m n : nat, S (m + n) = m + S n ).
(* plus_n_Sm: ∏ n m : nat, S (n + m) = n + S m *)
Search (forall m n l : nat, (m * n) * l = m * (n * l)).
(* natmultassoc: ∏ n m k : nat, n * m * k = n * (m * k) *)
Theorem exp_hom {l m n : nat} : exp l (m + n) = (exp l m) * (exp l n).
Proof.
  induction n as [|n IH].
  - simpl.
    transitivity (exp l m).
    + apply maponpaths.
      exact (natplusr0 m).
    + rewrite (natmultr1 (exp l m)).
      reflexivity.
  - simpl.
    transitivity (exp l (m + n) * l).
    + transitivity (exp l (S (m + n))).
      * apply maponpaths.
        symmetry.
        apply plus_n_Sm.
      * reflexivity.
    + transitivity ((exp l m * exp l n) * l).
      * apply (maponpaths (fun n : nat => n * l)).
        exact IH.
      * apply natmultassoc.
Qed.

(* Exercise 5 *)

Lemma path_combination {A : UU} {a a' b : A} (p : a = b) (q: a' = b) : a = a'.
Proof.
  transitivity b.
  exact p.
  symmetry.
  exact q.
Defined.

(* Exercise 6 *)

Lemma path_combination_fact {A : UU} {a b : A} (p : a = b) : idpath a = path_combination p p.
Proof.
  induction p.
  unfold path_combination.
  reflexivity.
Qed.