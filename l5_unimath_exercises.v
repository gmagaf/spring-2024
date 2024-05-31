Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* Show Lemma 11.1.2 of Rijke. Give Def 11.1.1 yourself. *)
Definition tot {A : UU} {B C : A → UU}
  (f : ∏ x : A, B x → C x) : (∑ x : A, B x) → (∑ x : A, C x).
Proof.
  intro s.
  set (a := pr1 s).
  set (b := pr2 s).
  use tpair.
  - exact a.
  - exact (f a b).
Defined.

(*
  Hint: Follow the proof in Rijke, using `isweq_iso` at the end.
   For the statements, you will want to use
  `hfiber`, `∘` (`funcomp`), `~` (`homot`), `≃` (`weq`).
*)

Lemma phi {A : UU} {B C : A → UU}
  (f : ∏ x : A, B x → C x) (t : ∑ x : A, C x) :
  hfiber (tot f) t → hfiber (f (pr1 t)) (pr2 t).
Proof.
  intro fib.
  unfold hfiber.
  induction fib as [ab p].
  induction p.
  use tpair.
  - exact (pr2 ab).
  - simpl.
    reflexivity.
Defined.

Lemma psi {A : UU} {B C : A → UU}
  (f : ∏ x : A, B x → C x) (t : ∑ x : A, C x) :
  hfiber (f (pr1 t)) (pr2 t) → hfiber (tot f) t.
Proof.
  intro fib.
  unfold hfiber in *.
  induction fib as [b p].
  use tpair.
  - exact (pr1 t,,b).
  - unfold tot.
    simpl.
    induction t as [a c].
    rewrite p.
    reflexivity.
Defined.

Lemma lemma_11_1_2 {A : UU} {B C : A → UU}
  (f : ∏ x : A, B x → C x) (t : ∑ x : A, C x) :
  hfiber (tot f) t ≃ hfiber (f (pr1 t)) (pr2 t).
Proof.
  use tpair.
  - exact (phi f t).
  - apply (isweq_iso (phi f t) (psi f t)).
    + intro fib.
      unfold hfiber in *.
      induction fib as [ab p].
      induction p.
      unfold tot.
      unfold psi.
      simpl.
      reflexivity.
    + intro fib.
      induction t as [a c].
      unfold hfiber in *.
      induction fib as [b p].
      simpl in *.
      unfold psi.
      unfold phi.
      induction p.
      simpl.
      reflexivity.
Defined.

(* Exercise 2 *)

(*
  Show that if two types are equivalent and one is contractible,
  then the other is.
*)

Print iscontr.
Theorem contr_is_equiv_invariant {A B : UU} : (iscontr A) → (A ≃ B) → iscontr B.
Proof.
  intro contr_a.
  intro e.
  induction contr_a as [a eq_a].
  induction e as [f equiv].
  use tpair.
  - exact (f a).
  - intro b.
    unfold isweq in equiv.
    induction (equiv b) as [[a' b_eq_fa'] _].
    transitivity (f a').
    + symmetry.
      exact b_eq_fa'.
    + apply maponpaths.
      apply eq_a.
Defined.

(*
  These proofs are starting to get more complicated,
  so you might want to the tactics `assert` or `transparent assert`.
  They basically let you prove small lemmas within your proof.
  If the lemma is not very small, I recommend making it a real lemma
  outside of your proof.
*)

(* For assert you type 
   `assert (x : T).`
   where T is some specific type that you want to prove.
   Then a new goal (T) will be added, and you can open that
   goal by using the bullets (i.e. `-`, `+`, etc) or by putting
   the proof in curly braces. Once you are done, you can move back
   to the original goal by using the same kind of bullet or
   closing the curly braces, and then x : T will be added to the
   list of hypotheses.
*)
(* If you want to use something about how x was constructed in
   the proof that follows, then you need `transparent assert`.
   Type:
   `transparent assert (x : (T)).`
   Note the extra parentheses.
*)

(* Exercise 3 *)

(* Show Theorem 11.1.3 of Rijke. *)

Theorem thm_11_1_3_a {A : UU} {B C : A → UU}
  (f : ∏ x : A, B x → C x)
  (feq : ∏ x : A, isweq (f x)) :
  isweq (tot f).
Proof.
  unfold isweq in *.
  intro ac.
  induction ac as [a c].
  apply (contr_is_equiv_invariant (A := hfiber (f a) c)).
  - apply feq.
  - Check lemma_11_1_2.
    Search (∏ A B : UU, A ≃ B -> B ≃ A).
    apply invweq.
    apply (lemma_11_1_2 f (a,,c)).
Defined.

Theorem thm_11_1_3_b {A : UU} {B C : A → UU}
  (f : ∏ x : A, B x → C x)
  (tot_eq : isweq (tot f)) :
  ∏ x : A, isweq (f x).
Proof.
  intro a.
  unfold isweq in *.
  intro c.
  apply (contr_is_equiv_invariant (A := hfiber (tot f) (a,,c))).
  - induction (tot_eq (a,,c)) as [[ab p] tot_fib_contr].
    use tpair.
    + exact (ab,,p).
    + exact tot_fib_contr.
  - apply lemma_11_1_2.
Defined.

(* Exercise 4 *)

(* Show Thm 11.4.2 of Rijke. *)

Lemma equiv_to_emb_lem_a {A B : UU} (f : A ≃ B) {a a' : A}: (a = a') → (f a = f a').
Proof.
  intro e.
  induction e.
  reflexivity.
Defined.

Lemma equiv_to_emb_lem_b {A B : UU} (f : A ≃ B) {a a' : A}: (f a = f a') → (a = a').
Proof.
  intro q.
  induction f as [f eq].
  induction (eq (f a)) as [[aa faa_fa] contr_aa].
  transitivity aa.
  - exact (maponpaths pr1 (contr_aa (a,,idpath (f a)))).
  - unfold hfiber in contr_aa.
    Check (contr_aa (a',, !q)).
    symmetry.
    exact (maponpaths pr1 (contr_aa (a',, !q))).
Defined.

Theorem thm_11_4_2 {A B : UU} (f : A ≃ B) {a a' : A} : isweq (equiv_to_emb_lem_a (a := a) (a' := a') f).
Proof.
  Check isweq_iso.
  apply (isweq_iso (equiv_to_emb_lem_a (a := a) (a' := a') f) (equiv_to_emb_lem_b (a := a) (a' := a') f)).
  - intro p.
    unfold equiv_to_emb_lem_b.
    unfold equiv_to_emb_lem_a.
    induction f as [f feq].
    simpl.
    induction p.
    simpl.
    admit.
  - intro q.
    unfold equiv_to_emb_lem_b.
    unfold equiv_to_emb_lem_a.
    induction f as [f feq].
    admit.
Admitted.
