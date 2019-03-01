(** An axiomatization of languages based on evaluation context items, including
    a proof that these are instances of general ectx-based languages. *)
From iris.algebra Require Export base.
From iris.program_logic Require Import language.
From atomic_block.program_logic Require Export atomic_ectx_language.
Set Default Proof Using "Type".

(* TAKE CARE: When you define an [ectxiLanguage] canonical structure for your
language, you need to also define a corresponding [language] and [ectxLanguage]
canonical structure for canonical structure inference to work properly. You
should use the coercion [EctxLanguageOfEctxi] and [LanguageOfEctx] for that, and
not [ectxi_lang] and [ectxi_lang_ectx], otherwise the canonical projections will
not point to the right terms.

A full concrete example of setting up your language can be found in [heap_lang].
Below you can find the relevant parts:

  Module heap_lang.
    (* Your language definition *)

    Lemma heap_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
    Proof. (* ... *) Qed.
  End heap_lang.

  Canonical Structure heap_ectxi_lang := EctxiLanguage heap_lang.heap_lang_mixin.
  Canonical Structure heap_ectx_lang := EctxLanguageOfEctxi heap_ectxi_lang.
  Canonical Structure heap_lang := LanguageOfEctx heap_ectx_lang.
*)

Section atomic_ectxi_language_mixin.
  Context {expr val ectx_item state observation : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (atomic_block_of : expr → option expr).
  Context (fill_item : ectx_item → expr → expr).
  Context (head_step : expr → state → list observation → expr → state → list expr → Prop).

  Record AtomicEctxiLanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_stuck e1 σ1 κ e2 σ2 efs : head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None;

    mixin_atomic_block_head_stuck e1 σ1 κ e2 σ2 efs :
      head_step e1 σ1 κ e2 σ2 efs → atomic_block_of e1 = None;
    mixin_atomic_block_not_val e ab :
      atomic_block_of e = Some ab → to_val e = None;
    mixin_atomic_block_no_ectx e ae:
      atomic_block_of e = Some ae → ∀ Ki e', e ≠ fill_item Ki e';

    mixin_fill_item_inj Ki : Inj (=) (=) (fill_item Ki);
    mixin_fill_item_val Ki e : is_Some (to_val (fill_item Ki e)) → is_Some (to_val e);
    mixin_fill_item_no_val_inj Ki1 Ki2 e1 e2 :
      to_val e1 = None → to_val e2 = None →
      fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2;

    mixin_head_ctx_step_val Ki e σ1 κ e2 σ2 efs :
      head_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e);
  }.
End atomic_ectxi_language_mixin.

Structure atomicectxiLanguage := AtomicEctxiLanguage {
  expr : Type;
  val : Type;
  ectx_item : Type;
  state : Type;
  observation : Type;

  of_val : val → expr;
  to_val : expr → option val;
  atomic_block_of : expr → option expr;
  fill_item : ectx_item → expr → expr;
  head_step : expr → state → list observation → expr → state → list expr → Prop;

  atomic_ectxi_language_mixin :
    AtomicEctxiLanguageMixin of_val to_val atomic_block_of fill_item head_step
}.

Arguments AtomicEctxiLanguage {_ _ _ _ _ _ _ _ _ _} _.
Arguments of_val {_} _%V.
Arguments to_val {_} _%E.
Arguments atomic_block_of {_} _%E.
Arguments fill_item {_} _ _%E.
Arguments head_step {_} _%E _ _ _%E _ _.

Section ectxi_language.
  Context {Λ : atomicectxiLanguage}.
  Implicit Types (e : expr Λ) (Ki : ectx_item Λ).
  Notation ectx := (list (ectx_item Λ)).

  (* Only project stuff out of the mixin that is not also in ectxLanguage *)
  Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. apply atomic_ectxi_language_mixin. Qed.
  Lemma fill_item_val Ki e : is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. apply atomic_ectxi_language_mixin. Qed.
  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof. apply atomic_ectxi_language_mixin. Qed.
  Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 efs :
    head_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
  Proof. apply atomic_ectxi_language_mixin. Qed.
  Lemma atomic_block_no_ectx e ae :
      atomic_block_of e = Some ae → ∀ Ki e', e ≠ fill_item Ki e'.
  Proof. apply atomic_ectxi_language_mixin. Qed.

  Definition fill (K : ectx) (e : expr Λ) : expr Λ := foldl (flip fill_item) e K.

  Lemma fill_app (K1 K2 : ectx) e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
  Proof. apply foldl_app. Qed.

  Definition atomic_ectxi_lang_ectx_mixin :
    AtomicEctxLanguageMixin
      of_val to_val atomic_block_of [] (flip (++)) fill head_step.
  Proof.
    assert (fill_val : ∀ K e, is_Some (to_val (fill K e)) → is_Some (to_val e)).
    { intros K. induction K as [|Ki K IH]=> e //=. by intros ?%IH%fill_item_val. }
    assert (fill_not_val : ∀ K e, to_val e = None → to_val (fill K e) = None).
    { intros K e. rewrite !eq_None_not_Some. eauto. }
    split.
    - apply atomic_ectxi_language_mixin.
    - apply atomic_ectxi_language_mixin.
    - apply atomic_ectxi_language_mixin.
    - intros K e1 σ1 κ e2 σ2 efs Hhstp.
      destruct K as [|? ? _] using rev_ind; first by eapply atomic_ectxi_language_mixin; eauto.
      rewrite fill_app /= in Hhstp.
      apply head_ctx_step_val, fill_val in Hhstp; destruct Hhstp as [? ?].
      destruct (atomic_block_of e1) eqn:Heqn; last done.
      eapply mixin_atomic_block_not_val in Heqn;
        eauto using atomic_ectxi_language_mixin.
      simplify_eq.
    - apply atomic_ectxi_language_mixin.
    - intros e ae Hae K e' He'.
      destruct K as [|? ? _] using rev_ind; simplify_eq; first done.
      rewrite fill_app /= in Hae.
      by pose proof (atomic_block_no_ectx _ _ Hae x (fill K e')).
    - done.
    - intros K1 K2 e. by rewrite /fill /= foldl_app.
    - intros K; induction K as [|Ki K IH]; rewrite /Inj; naive_solver.
    - done.
    - by intros [] [].
    - intros K K' e1 e1' ab Hnv Hfill Hab.
      revert K' Hfill.
      induction K as [|Ki K IH] using rev_ind => /= K' Hfill; eauto using app_nil_r.
      destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
      { rewrite fill_app /= in Hab.
          by pose proof (atomic_block_no_ectx _ _ Hab Ki (fill K e1)). }
      rewrite !fill_app /= in Hfill.
      assert (Ki = Ki') as ->.
      { eapply fill_item_no_val_inj, Hfill; eauto.
        apply fill_not_val. eapply mixin_atomic_block_not_val;
                              eauto using atomic_ectxi_language_mixin. }
      simplify_eq. destruct (IH K') as [K'' ->]; auto.
      exists K''. by rewrite assoc.
    - intros K K' e1 κ e1' σ1 e2 σ2 efs Hfill Hred Hstep; revert K' Hfill.
      induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
      destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
      { rewrite fill_app in Hstep. apply head_ctx_step_val in Hstep.
        apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. }
      rewrite !fill_app /= in Hfill.
      assert (Ki = Ki') as ->.
      { eapply fill_item_no_val_inj, Hfill; eauto using val_head_stuck.
        apply fill_not_val. revert Hstep. apply atomic_ectxi_language_mixin. }
      simplify_eq. destruct (IH K') as [K'' ->]; auto.
      exists K''. by rewrite assoc.
  Qed.

  Canonical Structure atomic_ectxi_lang_ectx :=
    AtomicEctxLanguage atomic_ectxi_lang_ectx_mixin.
  Canonical Structure atomic_ectxi_lang :=
    AtomicLanguageOfEctx atomic_ectxi_lang_ectx.

  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Lemma ectxi_language_sub_redexes_are_values e :
    (∀ Ki e', e = fill_item Ki e' → is_Some (to_val e')) →
    sub_redexes_are_values e.
  Proof.
    intros Hsub K e' ->. destruct K as [|Ki K _] using @rev_ind=> //=.
    intros []%eq_None_not_Some. eapply fill_val, Hsub. by rewrite /= fill_app.
  Qed.

  Global Instance ectxi_lang_ctx_item Ki : LanguageCtx (fill_item Ki).
  Proof. change (LanguageCtx (fill [Ki])). apply _. Qed.
End ectxi_language.

Arguments fill {_} _ _%E.
Arguments atomic_ectxi_lang_ectx : clear implicits.
Arguments atomic_ectxi_lang : clear implicits.
Coercion atomic_ectxi_lang_ectx : atomicectxiLanguage >-> atomicectxLanguage.
Coercion atomic_ectxi_lang : atomicectxiLanguage >-> language.

Definition EctxLanguageOfEctxi (Λ : atomicectxiLanguage) : atomicectxLanguage :=
  let '@AtomicEctxiLanguage E V C St K of_val to_val atomic_block_of fill head mix := Λ in
  @AtomicEctxLanguage E V (list C) St K of_val to_val atomic_block_of _ _ _ _
    (@atomic_ectxi_lang_ectx_mixin (@AtomicEctxiLanguage E V C St K of_val to_val atomic_block_of fill head mix)).
