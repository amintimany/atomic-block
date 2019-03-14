(** An axiomatization of evaluation-context based languages, including a proof
    that this gives rise to a "language" in the Iris sense. *)
From iris.algebra Require Export base.
From iris.program_logic Require Import language.
Set Default Proof Using "Type".

(* TAKE CARE: When you define an [ectxLanguage] canonical structure for your
language, you need to also define a corresponding [language] canonical
structure. Use the coercion [LanguageOfEctx] as defined in the bottom of this
file for doing that. *)

Section atomic_ectx_language_mixin.
  Context {expr val ectx state observation : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (atomic_block_of : expr → option expr).
  Context (empty_ectx : ectx).
  Context (comp_ectx : ectx → ectx → ectx).
  Context (fill : ectx → expr → expr).
  Context (head_step : expr → state → list observation → expr → state → list expr → Prop).

  Record AtomicEctxLanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_head_stuck e1 σ1 κ e2 σ2 efs :
      head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None;

    mixin_atomic_block_head_stuck K e1 σ1 κ e2 σ2 efs :
      head_step (fill K e1) σ1 κ e2 σ2 efs → atomic_block_of e1 = None;
    mixin_atomic_block_not_val e ab :
      atomic_block_of e = Some ab → to_val e = None;
    mixin_atomic_block_no_ectx e ae:
      atomic_block_of e = Some ae → ∀ K e', e = fill K e' → K = empty_ectx;

    mixin_fill_empty e : fill empty_ectx e = e;
    mixin_fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
    mixin_fill_inj K : Inj (=) (=) (fill K);
    mixin_fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e);

    (* There are a whole lot of sensible axioms (like associativity, and left and
    right identity, we could demand for [comp_ectx] and [empty_ectx]. However,
    positivity suffices. *)
    mixin_ectx_positive K1 K2 :
      comp_ectx K1 K2 = empty_ectx → K1 = empty_ectx ∧ K2 = empty_ectx;

    mixin_atomic_block_under_ectx K K' e1 e1' ab :
      to_val e1 = None →
      fill K e1 = fill K' e1' →
      atomic_block_of e1' = Some ab →
      ∃ K'', K' = comp_ectx K K'';

    mixin_step_by_val K K' e1 e1' σ1 κ e2 σ2 efs :
      fill K e1 = fill K' e1' →
      to_val e1 = None →
      head_step e1' σ1 κ e2 σ2 efs →
      ∃ K'', K' = comp_ectx K K'';
  }.
End atomic_ectx_language_mixin.

Structure atomicectxLanguage := AtomicEctxLanguage {
  expr : Type;
  val : Type;
  ectx : Type;
  state : Type;
  observation : Type;

  of_val : val → expr;
  to_val : expr → option val;
  atomic_block_of : expr → option expr;
  empty_ectx : ectx;
  comp_ectx : ectx → ectx → ectx;
  fill : ectx → expr → expr;
  head_step : expr → state → list observation → expr → state → list expr → Prop;

  atomic_ectx_language_mixin :
    AtomicEctxLanguageMixin
      of_val to_val atomic_block_of empty_ectx comp_ectx fill head_step
}.

Arguments AtomicEctxLanguage {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments of_val {_} _%V.
Arguments to_val {_} _%E.
Arguments atomic_block_of {_} _%E.
Arguments empty_ectx {_}.
Arguments comp_ectx {_} _ _.
Arguments fill {_} _ _%E.
Arguments head_step {_} _%E _ _ _%E _ _.

(* From an ectx_language, we can construct a language. *)
Section ectx_language.
  Context {Λ : atomicectxLanguage}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types K : ectx Λ.

  (* Only project stuff out of the mixin that is not also in language *)
  Lemma val_head_stuck e1 σ1 κ e2 σ2 efs : head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
  Proof. apply atomic_ectx_language_mixin. Qed.
  Lemma fill_empty e : fill empty_ectx e = e.
  Proof. apply atomic_ectx_language_mixin. Qed.
  Lemma fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof. apply atomic_ectx_language_mixin. Qed.
  Global Instance fill_inj K : Inj (=) (=) (fill K).
  Proof. apply atomic_ectx_language_mixin. Qed.
  Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof. apply atomic_ectx_language_mixin. Qed.
  Lemma ectx_positive K1 K2 :
    comp_ectx K1 K2 = empty_ectx → K1 = empty_ectx ∧ K2 = empty_ectx.
  Proof. apply atomic_ectx_language_mixin. Qed.
  Lemma step_by_val K K' e1 e1' σ1 κ e2 σ2 efs :
    fill K e1 = fill K' e1' →
    to_val e1 = None →
    head_step e1' σ1 κ e2 σ2 efs →
    ∃ K'', K' = comp_ectx K K''.
  Proof. apply atomic_ectx_language_mixin. Qed.
  Lemma atomic_block_head_stuck K e1 σ1 κ e2 σ2 efs :
    head_step (fill K e1) σ1 κ e2 σ2 efs → atomic_block_of e1 = None.
  Proof. apply atomic_ectx_language_mixin. Qed.
  Lemma atomic_block_head_stuck' e1 σ1 κ e2 σ2 efs :
    head_step e1 σ1 κ e2 σ2 efs → atomic_block_of e1 = None.
  Proof.
    pose proof (atomic_block_head_stuck empty_ectx e1 σ1 κ e2 σ2 efs) as Habhs.
    by rewrite fill_empty in Habhs.
  Qed.
  Lemma atomic_block_not_val e ab :
    atomic_block_of e = Some ab → to_val e = None.
  Proof. apply atomic_ectx_language_mixin. Qed.
  Lemma atomic_block_no_ectx e ae:
    atomic_block_of e = Some ae → ∀ K e', e = fill K e' → K = empty_ectx.
  Proof. apply atomic_ectx_language_mixin. Qed.
  Lemma atomic_block_under_ectx K K' e1 e1' ab :
    to_val e1 = None →
    fill K e1 = fill K' e1' →
    atomic_block_of e1' = Some ab →
    ∃ K'', K' = comp_ectx K K''.
  Proof. apply atomic_ectx_language_mixin. Qed.

  Definition head_reducible (e : expr Λ) (σ : state Λ) :=
    ∃ κ e' σ' efs, head_step e σ κ e' σ' efs.
  Definition head_reducible_no_obs (e : expr Λ) (σ : state Λ) :=
    ∃ e' σ' efs, head_step e σ [] e' σ' efs.
  Definition head_irreducible (e : expr Λ) (σ : state Λ) :=
    ∀ κ e' σ' efs, ¬head_step e σ κ e' σ' efs.
  Definition head_stuck (e : expr Λ) (σ : state Λ) :=
    to_val e = None ∧ head_irreducible e σ.

  (* All non-value redexes are at the root.  In other words, all sub-redexes are
     values. *)
  Definition sub_redexes_are_values (e : expr Λ) :=
    ∀ K e', e = fill K e' → to_val e' = None → K = empty_ectx.

  Inductive prim_step
            (e1 : expr Λ) (σ1 : state Λ) (κ : list (observation Λ))
            (e2 : expr Λ) (σ2 : state Λ) : list (expr Λ) → Prop :=
    Ectx_step K e1' e2' efs :
      e1 = fill K e1' → e2 = fill K e2' →
      head_step e1' σ1 κ e2' σ2 efs →
      prim_step e1 σ1 κ e2 σ2 efs
  | Atomic_bloack_step K e1' e2' ab :
      e1 = fill K e1' → e2 = fill K e2' →
      atomic_block_of e1' = Some ab →
      steps_atomically ab σ1 κ e2' σ2 →
      prim_step e1 σ1 κ e2 σ2 []
  with steps_atomically (e1 : expr Λ) (σ1 : state Λ) (κ : list (observation Λ))
            (e2 : expr Λ) (σ2 : state Λ) : Prop :=
  | Val_steps_atomic v :
      to_val e1 = Some v →
      to_val e2 = Some v →
      σ1 = σ2 →
      κ = [] →
      steps_atomically e1 σ1 κ e2 σ2
  | Prim_step_in_atomic_block e1' σ1' κ1' κ':
      κ = κ1' ++ κ' →
      prim_step e1 σ1 κ1' e1' σ1' [] →
      steps_atomically e1' σ1' κ' e2 σ2 →
      steps_atomically e1 σ1 κ e2 σ2.

  Lemma steps_atomically_always_to_val e1 σ1 κ e2 σ2 :
    steps_atomically e1 σ1 κ e2 σ2 → ∃ v, to_val e2 = Some v.
  Proof. induction 1; simplify_eq; eauto. Qed.

  Definition atomically_reducible (ab : expr Λ) (σ : state Λ) :=
    ∃ κ σ2 e2, steps_atomically ab σ κ e2 σ2.
  Definition atomically_irreducible (ab : expr Λ) (σ : state Λ) :=
    ∀ κ σ2 e2, ¬ steps_atomically ab σ κ e2 σ2.

  Lemma not_atomically_reducible (ab : expr Λ) (σ : state Λ) :
    ¬ atomically_reducible ab σ ↔ atomically_irreducible ab σ.
  Proof. firstorder. Qed.

  Lemma Ectx_step' K e1 σ1 κ e2 σ2 efs :
    head_step e1 σ1 κ e2 σ2 efs → prim_step (fill K e1) σ1 κ (fill K e2) σ2 efs.
  Proof. econstructor; eauto. Qed.

  Lemma val_prim_stuck e σ κ e' σ' efs :
    prim_step e σ κ e' σ' efs → to_val e = None.
  Proof.
    destruct 1 as [? ? ? ? ? ? ?%val_head_stuck|]; simplify_eq.
    - apply eq_None_not_Some. by intros ?%fill_val%eq_None_not_Some.
    - apply eq_None_not_Some. intros ?%fill_val%eq_None_not_Some; auto.
      eauto using atomic_block_not_val.
  Qed.

  Definition ectx_lang_mixin : LanguageMixin of_val to_val prim_step.
  Proof.
    split.
    - apply atomic_ectx_language_mixin.
    - apply atomic_ectx_language_mixin.
    - apply val_prim_stuck.
  Qed.

  Canonical Structure atomic_ectx_lang : language := Language ectx_lang_mixin.

  Definition head_atomic (a : atomicity) (e : expr Λ) : Prop :=
    ∀ σ κ e' σ' efs,
      head_step e σ κ e' σ' efs →
      if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e').

  (* Some lemmas about this language *)
  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Lemma head_prim_step e1 σ1 κ e2 σ2 efs :
    head_step e1 σ1 κ e2 σ2 efs → prim_step e1 σ1 κ e2 σ2 efs.
  Proof. apply Ectx_step with empty_ectx; by rewrite ?fill_empty. Qed.

  Lemma head_reducible_no_obs_reducible e σ :
    head_reducible_no_obs e σ → head_reducible e σ.
  Proof. intros (?&?&?&?). eexists. eauto. Qed.
  Lemma not_head_reducible e σ : ¬head_reducible e σ ↔ head_irreducible e σ.
  Proof. unfold head_reducible, head_irreducible. naive_solver. Qed.

  Lemma head_prim_reducible e σ : head_reducible e σ → reducible e σ.
  Proof. intros (κ&e'&σ'&efs&?). eexists κ, e', σ', efs. by apply head_prim_step. Qed.
  Lemma head_prim_reducible_no_obs e σ : head_reducible_no_obs e σ → reducible_no_obs e σ.
  Proof. intros (e'&σ'&efs&?). eexists e', σ', efs. by apply head_prim_step. Qed.
  Lemma head_prim_irreducible e σ : irreducible e σ → head_irreducible e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using head_prim_reducible.
  Qed.

  Lemma prim_head_reducible e σ :
    reducible e σ → sub_redexes_are_values e →
    atomic_block_of e = None → head_reducible e σ.
  Proof.
    intros (κ&e'&σ'&efs&[K e1' e2' ? ? Hstep|]) Hse Habo; simplify_eq.
    - assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
      rewrite fill_empty /head_reducible; eauto.
    - assert (K = empty_ectx); simplify_eq.
      { eapply Hse; eauto using atomic_block_not_val. }
      rewrite fill_empty in Habo; simplify_eq.
  Qed.
  Lemma prim_head_irreducible e σ :
    head_irreducible e σ → atomic_block_of e = None →
    sub_redexes_are_values e → irreducible e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using prim_head_reducible.
  Qed.

  Lemma head_stuck_stuck e σ :
    head_stuck e σ → sub_redexes_are_values e → atomic_block_of e = None
    → stuck e σ.
  Proof.
    intros [] ?. split; first done.
    by apply prim_head_irreducible.
  Qed.

  Lemma atomic_ectx_language_atomic a e :
    head_atomic a e → sub_redexes_are_values e →
    atomic_block_of e = None → Atomic a e.
  Proof.
    intros Hatomic_step Hse Hatomic_fill σ κ e' σ' efs [K e1' e2' ? ? ? ?|];
      simplify_eq.
    - assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
      rewrite fill_empty. eapply Hatomic_step. by rewrite fill_empty.
    - assert (K = empty_ectx); simplify_eq.
      { eapply Hse; eauto using atomic_block_not_val. }
      rewrite fill_empty in Hatomic_fill; simplify_eq.
  Qed.

  Lemma atomic_ectx_language_atomic_block_atomic a e ab :
    (∀ σ, reducible e σ) → atomic_block_of e = Some ab → Atomic a e.
  Proof.
    intros Hrd Hatomic_fill σ κ e' σ' efs
           [K e1' e2' ? ? ? Hstep|? ? ? ? ? ? _ Hsa]; simplify_eq.
    - eapply atomic_block_head_stuck' in Hstep.
      assert (K = empty_ectx); simplify_eq.
      { eapply atomic_block_no_ectx; eauto. }
      by rewrite fill_empty in Hatomic_fill; simplify_eq.
    - assert (K = empty_ectx); simplify_eq.
      { eapply atomic_block_no_ectx; eauto. }
      rewrite fill_empty.
      induction Hsa; simplify_eq; auto.
      destruct a; try apply val_irreducible; by eauto.
  Qed.

  Lemma head_reducible_prim_step e1 σ1 κ e2 σ2 efs :
    head_reducible e1 σ1 →
    prim_step e1 σ1 κ e2 σ2 efs →
    head_step e1 σ1 κ e2 σ2 efs.
  Proof.
    intros (κ'&e2''&σ2''&efs''&Hhstp)
           [K e1' e2' ? -> -> Hstep|? ? ? ab ? ? Hsa]; simplify_eq.
    - destruct (step_by_val K empty_ectx e1' (fill K e1') σ1 κ' e2'' σ2'' efs'')
      as [K' [-> _]%symmetry%ectx_positive];
      eauto using fill_empty, fill_not_val, val_head_stuck.
      by rewrite !fill_empty.
    - by erewrite atomic_block_head_stuck in Hsa; eauto.
  Qed.

  Lemma atomic_block_prim_step ab e1 σ1 κ e2 σ2 efs :
    atomic_block_of e1 = Some ab →
    prim_step e1 σ1 κ e2 σ2 efs →
    steps_atomically ab σ1 κ e2 σ2 ∧ efs = [].
  Proof.
    intros Hab
           [K e1' e2' ? -> -> Hstep|? ? ? ab' ? ? Hsa]; simplify_eq.
    - destruct (atomic_block_under_ectx K empty_ectx e1' (fill K e1') ab)
      as [K' [-> _]%symmetry%ectx_positive];
      eauto using fill_empty, fill_not_val, val_head_stuck.
      erewrite (atomic_block_head_stuck empty_ectx) in Hab;
        by rewrite ?fill_empty.
    - destruct (atomic_block_under_ectx K empty_ectx e1' (fill K e1') ab)
        as [K' [? ?]%symmetry%ectx_positive]; simplify_eq; rewrite ?fill_empty //.
      { eapply atomic_block_not_val; eauto. }
      by rewrite fill_empty in Hab; simplify_eq.
  Qed.

  (* Every evaluation context is a context. *)
  Global Instance ectx_lang_ctx K : LanguageCtx (fill K).
  Proof.
    split; simpl.
    - eauto using fill_not_val.
    - intros ?????? [K' e1' e2' ? Heq1 Heq2 Hstep|K' e1' e2']; simplify_eq.
      + by apply (Ectx_step _ _ _ _ _ (comp_ectx K K') e1' e2');
          rewrite ?fill_comp.
      + rewrite ?fill_comp.
        eapply (Atomic_bloack_step _ _ _ _ _ (comp_ectx K K') e1' e2'); eauto.
    - intros e1 σ1 κ e2 σ2 ? Hnval Hpstp.
      inversion Hpstp as [K'' e1'' e2'' ? Heq1 -> Hstep|K'' e1'' e2'' ab Heq1];
        simplify_eq.
      + destruct (step_by_val K K'' e1 e1'' σ1 κ e2'' σ2 efs) as [K' ->]; eauto.
        rewrite -fill_comp in Heq1; apply (inj (fill _)) in Heq1.
        exists (fill K' e2''); rewrite -fill_comp; split; auto.
        econstructor; eauto.
      + destruct (atomic_block_under_ectx K K'' e1 e1'' ab) as [K' ->]; eauto.
        rewrite -fill_comp in Heq1; apply (inj (fill _)) in Heq1.
        exists (fill K' e2''); rewrite -fill_comp; split; auto.
        econstructor 2; eauto.
  Qed.

  Record pure_head_step (e1 e2 : expr Λ) := {
    pure_head_step_safe σ1 : head_reducible_no_obs e1 σ1;
    pure_head_step_det σ1 κ e2' σ2 efs :
      head_step e1 σ1 κ e2' σ2 efs → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs = []
  }.

  Lemma pure_head_step_pure_step e1 e2 : pure_head_step e1 e2 → pure_step e1 e2.
  Proof.
    intros [Hp1 Hp2]. split.
    - intros σ. destruct (Hp1 σ) as (e2' & σ2 & efs & ?).
      eexists e2', σ2, efs. by apply head_prim_step.
    - intros σ1 κ e2' σ2 efs ?%head_reducible_prim_step;
        eauto using head_reducible_no_obs_reducible.
  Qed.

  Lemma atomically_reducible_reducible e ab σ :
    atomic_block_of e = Some ab → atomically_reducible ab σ → reducible e σ.
  Proof.
    intros ?(?&?&?&?).
    eexists _, _, _, _.
    eapply (Atomic_bloack_step _ _ _ _ _ empty_ectx); rewrite ?fill_empty; eauto.
  Qed.

  Lemma prim_atomically_reducible e ab σ :
    reducible e σ → atomic_block_of e = Some ab → atomically_reducible ab σ.
  Proof.
    intros (κ&e'&σ'&efs&[K e1' e2' ? ? ? Hstep|? ? ? ab']) Hab; simplify_eq.
    - assert (K = empty_ectx); simplify_eq.
      { eapply atomic_block_no_ectx; eauto. }
      rewrite fill_empty in Hab; simplify_eq.
      apply atomic_block_head_stuck' in Hstep; simplify_eq.
    - assert (K = empty_ectx); simplify_eq.
      { eapply atomic_block_no_ectx; eauto. }
      rewrite fill_empty in Hab; simplify_eq.
      eexists _, _, _; eauto.
  Qed.
  Lemma atomic_block_irreducible e ab σ :
    atomic_block_of e = Some ab → atomically_irreducible ab σ → irreducible e σ.
  Proof.
    rewrite -not_atomically_reducible -not_reducible.
    eauto using prim_atomically_reducible.
  Qed.

  Lemma atomically_irreducible_stuck e ab σ :
    atomic_block_of e = Some ab → atomically_irreducible ab σ → stuck e σ.
  Proof.
    intros.
    split; simpl; eauto using atomic_block_irreducible, atomic_block_not_val.
  Qed.

  Global Instance pure_exec_fill K φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (fill K e1) (fill K e2).
  Proof. apply: pure_exec_ctx. Qed.
End ectx_language.

Arguments atomic_ectx_lang : clear implicits.
Coercion atomic_ectx_lang : atomicectxLanguage >-> language.

(* This definition makes sure that the fields of the [language] record do not
refer to the projections of the [ectxLanguage] record but to the actual fields
of the [ectxLanguage] record. This is crucial for canonical structure search to
work.

Note that this trick no longer works when we switch to canonical projections
because then the pattern match [let '...] will be desugared into projections. *)
Definition AtomicLanguageOfEctx (Λ : atomicectxLanguage) : language :=
  let '@AtomicEctxLanguage E V C St K of_val to_val atomic_block_of empty comp fill head mix := Λ in
  @Language E V St K of_val to_val _
    (@ectx_lang_mixin (@AtomicEctxLanguage E V C St K of_val to_val atomic_block_of empty comp fill head mix)).
