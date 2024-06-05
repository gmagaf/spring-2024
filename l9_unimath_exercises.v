(** * l9 Exercises *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.NumberSystems.All.

(**                   **)
(** * Preliminaries * **)
(**                   **)

Variable funext : funextsecStatement.

(** Generalisation of [maponpaths] to dependent functions. *)
(** Called [apd] in the lecture *)
Definition maponpaths_dep {X:UU} {Y : X -> UU}
    (f : ∏ x:X, Y x) {x1 x2} (e : x1 = x2)
  : transportf _ e (f x1) = f x2.
Proof.
  induction e.
  apply idpath.
Defined.

(** A circle is something that looks like a circle! *)
Definition circle_ind_structure {S : UU} {b : S} (l : b = b) : UU
  := ∏ (Y : S -> UU) (y_b : Y b) (y_l : transportf _ l y_b = y_b),
  (* The dependent function *)
   ∑ (f : ∏ x:S, Y x)
  (* The computation rule for the basepoint *)
     (e_b : f b = y_b),
  (* The computation rule for the loop, note that
     some paths have been added for it to typecheck *)
       maponpaths_dep f l
     = (maponpaths _ e_b) @ y_l @ !e_b.

(** From now on, we fix a circle type *)
Context {S1 : UU} {base : S1} (loop : base = base)
  (circle_str : circle_ind_structure loop).

(* For ease of use, we provide "accessors" to the relevant data *)
Definition circle_ind
    {Y : S1 -> UU} {y_b : Y base} (y_l : transportf _ loop y_b = y_b)
  : ∏ x:S1, Y x.
Proof.
  exact (pr1 (circle_str _ _ y_l)).
Defined.

Definition circle_ind_comp_base
    {Y : S1 -> UU} {y_b : Y base} (y_l : transportf _ loop y_b = y_b)
  : circle_ind y_l base = y_b.
Proof.
  exact (pr12 (circle_str _ _ y_l)).
Defined.

Definition circle_ind_comp_loop
    {Y : S1 -> UU} {y_b : Y base} (y_l : transportf _ loop y_b = y_b)
  : maponpaths_dep (circle_ind y_l) loop
  = maponpaths _ (circle_ind_comp_base _)
    @ y_l @ ! (circle_ind_comp_base _).
Proof.
  exact (pr22 (circle_str _ _ y_l)).
Defined.

(**                   **)
(** * Exercises     * **)
(**                   **)

(* Exercise 1 *, The uniqueness principle *)
(* Hint: you may need [pathscomp0rid] and you will need
   to state your own lemma(s) *)

Lemma transp_loop_along_path
    {Y : UU}{x y : Y}
    (l : x = x)
    (p : x = y) :
    transportf (λ y : Y, y = y) p l = !p @ l @ p.
Proof.
  induction p.
  simpl.
  transitivity l.
  - reflexivity.
  - induction l.
    reflexivity.
Qed.

Lemma transp_path_along_loop
    {X Y : UU}{f g : X -> Y}{x : X}
    (l : x = x)
    (p : f x = g x) :
    transportf (λ x : X, f x = g x) l p = !(maponpaths f l) @ p @ (maponpaths g l).
Proof.
  induction l.
  simpl.
  transitivity p.
  - reflexivity.
  - induction p.
    reflexivity.
Qed.

Lemma technical_lemma {X : UU}{x y z w : X}
  (l1 : x = y)
  (p : y = z)
  (l2 : w = z)
  (q : x = w) : l2 = ! q @ l1 @ p → ! l1 @ q @ l2 = p.
Proof.
  intro s.
  induction p.
  induction q.
  induction l1.
  simpl.
  simpl in s.
  exact s.
Qed.

Definition circle_uniq
    {Y : UU} {f g : S1 -> Y}
    (p : f base = g base)
    (q : transportf (λ y : Y, y = y) p (maponpaths f loop) = maponpaths g loop) :
    ∏ (x : S1), f x = g x.
Proof.
  apply (circle_ind (Y := λ x : S1, f x = g x) (y_b := p)).
  assert (transportf (λ x : S1, f x = g x) loop p =
          !(maponpaths f loop) @ p @ (maponpaths g loop)) as l1.
  {
    apply transp_path_along_loop.
  }
  assert (!(maponpaths f loop) @ p @ (maponpaths g loop) = p) as l2.
  {
    clear l1.
    set (lem := transp_loop_along_path (Y := Y) (x := f base) (y := g base) (maponpaths f loop) p).
    set (s := !q @ lem).
    apply technical_lemma.
    exact s.
  }
  exact (l1 @ l2).
Qed.

(* Exercise 2 *, The non-dependent induction principle *)
(* Hint, you will probably need [transportf_const] and [eqtohomot] *)

Definition circle_rec
    {Y : UU} {y_b : Y} (y_l : y_b = y_b)
  : S1 → Y.
Proof.
  apply (circle_ind (Y := fun _ => Y) (y_b := y_b)).
  set (p := maponpaths (fun f => f y_b) (transportf_const loop Y)).
  simpl in p.
  exact (p @ y_l).
Defined.

Definition circle_rec_comp_base
    {Y : UU} {y_b : Y} (y_l : y_b = y_b)
  : circle_rec y_l base = y_b.
Proof.
  unfold circle_rec.
  set (p := maponpaths (fun f => f y_b) (transportf_const loop Y)).
  simpl in p.
  exact (circle_ind_comp_base (Y := fun _ => Y) (y_b := y_b) (p @ y_l)).
Defined.

(* Hint, you will need a coherence lemma *)
Check maponpaths_dep.
Check transportf_const.

Lemma not_dep_maponpaths_is_not_dep
    {X:UU} {Y : UU} {x1 x2 : X}
    (f : X → Y)
    (e : x1 = x2) :
    maponpaths_dep f e =
    (maponpaths (fun g => g (f x1)) (transportf_const e Y)) @ maponpaths f e.
Proof.
  induction e.
  simpl.
  reflexivity.
Qed.

Lemma left_inv
    {X : UU}{x y z : X}(p : y = z) (q : x = y) : !q @ q @ p = p.
Proof.
  induction p.
  induction q.
  reflexivity.
Qed.

Lemma assoc {Y : UU} : ∏ a b c d : Y, ∏ p : a = b, ∏ q : b = c, ∏ r : c = d, (p @ q) @ r = p @ q @ r.
Proof.
  intros.
  induction p.
  induction q.
  induction r.
  reflexivity.
Qed.

Definition circle_rec_comp_loop
    {Y : UU} {y_b : Y} (y_l : y_b = y_b)
  : maponpaths (circle_rec y_l) loop
  = circle_rec_comp_base y_l @ y_l @ ! circle_rec_comp_base y_l.
Proof.
  unfold circle_rec.
  unfold circle_rec_comp_base.
  set (p := maponpaths (fun f => f y_b) (transportf_const loop Y)).
  simpl in p.
  set (s := circle_ind_comp_loop (Y := fun _ => Y) (y_b := y_b) (p @ y_l)).
  rewrite assoc in s.
  rewrite !(not_dep_maponpaths_is_not_dep (circle_ind (p @ y_l)) loop) in s.
  assert (lem : ∏ fb y_b : Y, ∏ base_p : fb = y_b,
          !maponpaths (λ g : Y → Y, g fb) (transportf_const loop Y) @
          maponpaths (transportf (λ _ : S1, Y) loop) base_p @
          (maponpaths (λ f : Y → Y, f y_b) (transportf_const loop Y))
           = base_p).
  {
    induction base_p.
    simpl.
    exact (pathsinv0l (maponpaths (λ f : Y → Y, f fb) (transportf_const loop Y))).
  }
  set (lemInst := lem (circle_ind (p @ y_l) base) y_b (circle_ind_comp_base (p @ y_l))).
  set (s2 := maponpaths (fun pp => !maponpaths (λ g : Y → Y, g (circle_ind (p @ y_l) base))
      (transportf_const loop Y) @ pp) s).
  simpl in s2.
  transitivity (! maponpaths (λ g : Y → Y, g (circle_ind (p @ y_l) base))
       (transportf_const loop Y) @
   maponpaths (λ g : Y → Y, g (circle_ind (p @ y_l) base))
     (transportf_const loop Y) @
   maponpaths (circle_ind (p @ y_l)) loop).
  - exact (!left_inv _ _).
  - transitivity (! maponpaths (λ g : Y → Y, g (circle_ind (p @ y_l) base))
       (transportf_const loop Y) @
   maponpaths (transportf (λ _ : S1, Y) loop)
     (circle_ind_comp_base (p @ y_l)) @
   p @ y_l @ ! circle_ind_comp_base (p @ y_l)).
    + exact s2.
    + simpl.
      clear s2.
      clear s.
      Check (maponpaths (fun pp => pp @ y_l @ ! circle_ind_comp_base ((maponpaths (λ f : Y → Y, f y_b) (transportf_const loop Y)) @ y_l)) lemInst).
      transitivity ((! maponpaths (λ g : Y → Y, g (circle_ind (p @ y_l) base))
            (transportf_const loop Y) @
        maponpaths (transportf (λ _ : S1, Y) loop)
          (circle_ind_comp_base (p @ y_l)) @
        maponpaths (λ f : Y → Y, f y_b) (transportf_const loop Y)) @
       y_l @
       ! circle_ind_comp_base
           (maponpaths (λ f : Y → Y, f y_b)
              (transportf_const loop Y) @ y_l)).
      * clear lemInst lem.
        rewrite assoc.
        rewrite assoc.
        reflexivity.
      * exact (maponpaths (fun pp => pp @ y_l @ ! circle_ind_comp_base ((maponpaths (λ f : Y → Y, f y_b) (transportf_const loop Y)) @ y_l)) lemInst).
Defined.

(* Exercise 3 *, The universal principle *)
(* Hint: Use the above exercises and [total2_paths2_f] *)

Lemma lem {Y : UU} : ∏ a b : Y, ∏ q : a = b, ∏ l : b = b,
            transportf (λ y : Y, y = y) q (q @ l @ ! q) = l.
Proof.
  intros.
  induction q.
  simpl.
  Search (∏ A : UU, ∏ a b : A, ∏ p : a = b, p @ idpath b = p).
  rewrite (pathscomp0rid l).
  Search (∏ A : UU, ∏ B : A → UU, ∏ a : A, ∏ b : B a, transportf B (idpath a) b = b).
  apply (idpath_transportf (λ y : Y, y = y)).
Qed.

Definition circle_ump_structure (Y : UU) :
  isweq ((fun f => (f base,, maponpaths f loop)) : (S1 -> Y) -> (∑ y:Y, y = y)).
Proof.
  set (map := fun f : (S1 -> Y) => (f base,, maponpaths f loop) : (∑ y:Y, y = y)).
  set (ind := fun pair : ∑ y:Y, y = y => circle_rec (pr2 pair)).
  Check isweq_iso.
  apply (isweq_iso map ind).
  - intro f.
    unfold ind.
    unfold map.
    simpl.
    apply funextsec.
    unfold homot.
    Check circle_uniq.
    set (p := circle_rec_comp_base (maponpaths f loop)).
    apply (circle_uniq p).
    rewrite (circle_rec_comp_loop (maponpaths f loop)).
    apply lem.
  - intro pair.
    induction pair as [y_b y_l].
    unfold ind.
    unfold map.
    simpl.
    set (p := circle_rec_comp_base y_l).
    Check total2_paths2_f.
    apply (total2_paths2_f p).
    rewrite (circle_rec_comp_loop y_l).
    apply lem.
Qed.

(* Exercise 4 *, The suspension HIT *)
(* Give a definition of the suspension HIT as was done above for the circle *)

Definition ΣA_ind_structure (A : UU)
  {SA : UU} {i : A → SA} {n : SA} {s : SA} {merid : A → n = s} :=
  ∏ (Y : SA → UU)
    (y_i : ∏ a : A, Y (i a))
    (y_n : Y n)
    (y_s : Y s)
    (y_merid : ∏ a : A, transportf Y (merid a) y_n = y_s),
  ∑ (f : ∏ x : SA, Y x)
    (e_i : ∏ a : A, f (i a) = y_i a)
    (e_n : f n = y_n)
    (e_s : f s = y_s),
    ∏ a : A, maponpaths_dep f (merid a) = (maponpaths (transportf Y (merid a)) e_n) @ (y_merid a) @ !e_s.
