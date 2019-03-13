From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From iris.bi Require Import fixpoint big_op.
Set Default Proof Using "Type".
Import uPred.

(* Type class and Notation for atomic block WP's *)

Class ABwp (Λ : language) (PROP : Type) :=
  abwp : expr Λ → list (observation Λ) →
         (val Λ → list (observation Λ) → PROP) → PROP.
Arguments twp {_ _ _ _} _%E _ _%I.
Instance: Params (@twp) 5 := {}.

(** Notations for atomic block WP's *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'ABWP' e @ μs [{ Φ } ]" := (abwp e%E μs Φ)
  (at level 20, e, μs, Φ at level 200, only parsing) : bi_scope.
Notation "'ABWP' e [{ Φ } ]" := (abwp e%E [] Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder.  The indentation for the inner format block is chosen
such that *if* one has a single-character mask (e.g. [E]), the second line
should align with the binder(s) on the first line. *)
Notation "'ABWP' e @ μs [{ v ; κs , Q } ]" := (abwp e%E μs (λ v κs, Q))
  (at level 20, e, μs, Q at level 200,
   format "'[' 'ABWP'  e  '/' '[          ' @  μs [{  v ; κs ,  Q  } ] ']' ']'") : bi_scope.
Notation "'ABWP' e [{ v ; κs , Q } ]" := (abwp e%E [] (λ v κs, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'ABWP'  e  '/' '[       ' [{  v ; κs ,  Q  } ] ']' ']'") : bi_scope.

Definition abwp_pre `{irisG Λ Σ}
           (wp : expr Λ → list (observation Λ) →
                 (val Λ → list (observation Λ) → iProp Σ) → iProp Σ) :
  expr Λ → list (observation Λ) →
  (val Λ → list (observation Λ) → iProp Σ) → iProp Σ := λ e1 μs Φ,
  match to_val e1 with
  | Some v => |==> Φ v μs
  | None => ∀ σ1 κs n,
     state_interp σ1 κs n ==∗ ⌜reducible e1 σ1⌝ ∗
       ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ==∗
         ⌜efs = []⌝ ∗
         state_interp σ2 κs n ∗ wp e2 (μs ++ κ) Φ
  end%I.

Lemma abwp_pre_mono `{irisG Λ Σ}
    (wp1 wp2 : expr Λ → list (observation Λ) →
               (val Λ → list (observation Λ) → iProp Σ) → iProp Σ) :
  ((□ ∀ e μs Φ, wp1 e μs Φ -∗ wp2 e μs Φ) →
  ∀ e μs Φ, abwp_pre wp1 e μs Φ -∗ abwp_pre wp2 e μs Φ)%I.
Proof.
  iIntros "#H"; iIntros (e1 μs Φ) "Hwp". rewrite /abwp_pre.
  destruct (to_val e1) as [v|]; first done.
  iIntros (σ1 κs n) "Hσ". iMod ("Hwp" with "Hσ") as "($ & Hwp)"; iModIntro.
  iIntros (κ e2 σ2 efs) "Hstep".
  iMod ("Hwp" with "Hstep") as (?) "(Hσ & Hwp)".
  iModIntro. iFrame "Hσ"; iSplit; first done. by iApply "H".
Qed.

(* Uncurry [abwp_pre] and equip its type with an OFE structure *)
Definition abwp_pre' `{irisG Λ Σ} :
  (prodC (prodC (exprC Λ) (leibnizC (list (observation Λ))))
         (val Λ -c> (leibnizC (list (observation Λ))) -c> iProp Σ) → iProp Σ) →
  (prodC (prodC (exprC Λ) (leibnizC (list (observation Λ))))
         (val Λ -c> (leibnizC (list (observation Λ))) -c> iProp Σ) → iProp Σ)
  := curry3 ∘ abwp_pre ∘ uncurry3.

Local Instance abwp_pre_mono' `{irisG Λ Σ} : BiMonoPred (abwp_pre').
Proof.
  constructor.
  - iIntros (wp1 wp2) "#H"; iIntros ([[e1 μs] Φ]); iRevert (e1 μs Φ).
    iApply abwp_pre_mono. iIntros "!#" (e μs Φ). iApply ("H" $! (e, μs,Φ)).
  - intros wp Hwp n [[e1 μs] Φ1] [[e2 μs2] Φ2]
      [[?%leibniz_equiv ?%leibniz_equiv] HPhi]; simplify_eq/=.
    rewrite /uncurry3 /abwp_pre. do 23 (f_equiv || apply HPhi || done).
    by apply pair_ne.
Qed.

Definition abwp_def `{irisG Λ Σ}
    (e : expr Λ) (μs : list (observation Λ))
    (Φ : val Λ → (list (observation Λ)) → iProp Σ) :
  iProp Σ := bi_least_fixpoint (abwp_pre') (e,μs,Φ).
Definition abwp_aux `{irisG Λ Σ} : seal (@abwp_def Λ Σ _). by eexists. Qed.
Instance abwp' `{irisG Λ Σ} : ABwp Λ (iProp Σ) := abwp_aux.(unseal).
Definition abwp_eq `{irisG Λ Σ} : abwp = @abwp_def Λ Σ _ := abwp_aux.(seal_eq).

Section abwp.
Context `{irisG Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → (list (observation Λ)) → iProp Σ.
Implicit Types μs κs : list (observation Λ).
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma abwp_unfold e μs Φ : ABWP e @ μs [{ Φ }] ⊣⊢ abwp_pre abwp e μs Φ.
Proof. by rewrite abwp_eq /abwp_def least_fixpoint_unfold. Qed.
Lemma abwp_ind Ψ :
  (∀ n e μs, Proper (pointwise_relation _  (pointwise_relation _ (dist n)) ==> dist n) (Ψ e μs)) →
  (□ (∀ e μs Φ,
         abwp_pre (λ e μs Φ, Ψ e μs Φ ∧
                               ABWP e @ μs [{ Φ }]) e μs Φ -∗ Ψ e μs Φ) →
  ∀ e μs Φ, ABWP e @ μs [{ Φ }] -∗ Ψ e μs Φ)%I.
Proof.
  iIntros (HΨ). iIntros "#IH" (e μs Φ) "H". rewrite abwp_eq.
  set (Ψ' := curry3 Ψ :
    (prodC (prodC (exprC Λ) (leibnizC (list (observation Λ))))
         (val Λ -c> (leibnizC (list (observation Λ))) -c> iProp Σ) → iProp Σ)).
  assert (NonExpansive Ψ').
  { intros n [[e1 μs1] Φ1] [[e2 μs2] Φ2]
      [[?%leibniz_equiv ?%leibniz_equiv] ?]; simplify_eq/=.
      by apply HΨ. }
  iApply (least_fixpoint_strong_ind _ Ψ' with "[] H").
  iIntros "!#" ([[??] ?]) "H". by iApply "IH".
Qed.

Global Instance abwp_ne e μs n :
  Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==> dist n)
         (abwp (PROP:=iProp Σ) e μs).
Proof.
  intros Φ1 Φ2 HΦ. rewrite !abwp_eq. by apply (least_fixpoint_ne _), pair_ne, HΦ.
Qed.
Global Instance abwp_proper e μs :
  Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (≡))
         (abwp (PROP:=iProp Σ) e μs).
Proof.
  intros Φ Φ' HPhi; apply equiv_dist=>n; apply abwp_ne=>v μs'; apply equiv_dist.
  apply HPhi.
Qed.

Lemma abwp_value' Φ v μs : Φ v μs -∗ ABWP of_val v @ μs [{ Φ }].
Proof. iIntros "HΦ". rewrite abwp_unfold /abwp_pre to_of_val. auto. Qed.
Lemma abwp_value_inv' Φ v μs : ABWP of_val v @ μs [{ Φ }] ==∗ Φ v μs.
Proof. by rewrite abwp_unfold /abwp_pre to_of_val. Qed.

Lemma abwp_strong_mono e μs Φ Ψ :
  ABWP e @ μs [{ Φ }] -∗ (∀ v κs, Φ v κs ==∗ Ψ v κs) -∗ ABWP e @ μs [{ Ψ }].
Proof.
  iIntros "H HΦ". iRevert (Ψ) "HΦ"; iRevert (e μs Φ) "H".
  iApply abwp_ind; first solve_proper.
  iIntros "!#" (e μs Φ) "IH"; iIntros (Ψ) "HΦ".
  rewrite !abwp_unfold /abwp_pre. destruct (to_val e) as [v|] eqn:?.
  { by iApply ("HΦ" with "[> -]"). }
  iIntros (σ1 κs n) "Hσ".
  iMod ("IH" with "[$]") as "[% IH]".
  iModIntro; iSplit; first done. iIntros (κ e2 σ2 efs Hstep).
  iMod ("IH" with "[//]") as (?) "(Hσ & IH)"; auto.
  iModIntro.
  iFrame "Hσ". iSplit; first done.
  iDestruct "IH" as "[IH _]". iApply ("IH" with "HΦ").
Qed.

Lemma bupd_abwp e μs Φ : (|==> ABWP e @ μs [{ Φ }]) -∗ ABWP e @ μs [{ Φ }].
Proof.
  rewrite abwp_unfold /abwp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 κs n) "Hσ1". iMod "H". by iApply "H".
Qed.
Lemma abwp_bupd e μs Φ :
  ABWP e @ μs [{ v; κs, |==> Φ v κs }] -∗ ABWP e @ μs [{ Φ }].
Proof. iIntros "H". iApply (abwp_strong_mono with "H"); auto. Qed.

Lemma abwp_bind K `{!LanguageCtx K} μs e Φ :
  ABWP e @ μs [{ v ; κs, ABWP K (of_val v) @ κs [{ Φ }] }]
                 -∗ ABWP K e @ μs [{ Φ }].
Proof.
  revert Φ. cut (∀ Φ', ABWP e @ μs [{ Φ' }] -∗ ∀ Φ,
    (∀ v κs, Φ' v κs -∗ ABWP K (of_val v) @ κs [{ Φ }])
      -∗ ABWP K e @ μs [{ Φ }]).
  { iIntros (help Φ) "H". iApply (help with "H"); auto. }
  iIntros (Φ') "H". iRevert (e μs Φ') "H". iApply abwp_ind; first solve_proper.
  iIntros "!#" (e μs Φ') "IH". iIntros (Φ) "HΦ".
  rewrite /abwp_pre. destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iApply bupd_abwp. by iApply "HΦ". }
  rewrite abwp_unfold /abwp_pre fill_not_val //.
  iIntros (σ1 κs n) "Hσ". iMod ("IH" with "[$]") as "[% IH]". iModIntro; iSplit.
  { iPureIntro. unfold reducible in *.
    naive_solver eauto using fill_step. }
  iIntros (κ e2 σ2 efs Hstep).
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("IH" $! κ e2' σ2 efs with "[//]") as (?) "(Hσ & IH)".
  iModIntro. iFrame "Hσ". iSplit; first done.
  iDestruct "IH" as "[IH _]". by iApply "IH".
Qed.

Lemma abwp_bind_inv K `{!LanguageCtx K} μs e Φ :
  ABWP K e @ μs [{ Φ }] -∗ ABWP e @ μs [{ v; κs, ABWP K (of_val v) @ κs [{ Φ }] }].
Proof.
  iIntros "H". remember (K e) as e' eqn:He'.
  iRevert (e He'). iRevert (e' μs Φ) "H". iApply abwp_ind; first solve_proper.
  iIntros "!#" (e' μs Φ) "IH". iIntros (e ->).
  rewrite !abwp_unfold {2}/abwp_pre. destruct (to_val e) as [v|] eqn:He.
  { iModIntro. apply of_to_val in He as <-. rewrite !abwp_unfold.
    iApply (abwp_pre_mono with "[] IH"). by iIntros "!#" (e μs' Φ') "[_ ?]". }
  rewrite /abwp_pre fill_not_val //.
  iIntros (σ1 κs n) "Hσ". iMod ("IH" with "[$]") as "[% IH]". iModIntro; iSplit.
  { eauto using reducible_fill. }
  iIntros (κ e2 σ2 efs Hstep).
  iMod ("IH" $! κ (K e2) σ2 efs with "[]") as (?) "(Hσ & IH)"; eauto using fill_step.
  iModIntro. iFrame "Hσ". iSplit; first done.
  iDestruct "IH" as "[IH _]". by iApply "IH".
Qed.

(** * Derived rules *)
Lemma abwp_mono e μs Φ Ψ :
  (∀ v κs, Φ v κs -∗ Ψ v κs) → ABWP e @ μs [{ Φ }] -∗ ABWP e @ μs [{ Ψ }].
Proof.
  iIntros (HΦ) "H"; iApply (abwp_strong_mono with "H"); auto.
  iIntros (v κs) "?". by iApply HΦ.
Qed.

Global Instance abwp_mono' e μs:
  Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (⊢))
         (abwp (PROP:=iProp Σ) e μs).
Proof. by intros Φ Φ' ?; apply abwp_mono. Qed.

Lemma abwp_value Φ e μs v : IntoVal e v → Φ v μs -∗ ABWP e @ μs [{ Φ }].
Proof. intros <-. by apply abwp_value'. Qed.
Lemma abwp_value_bupd' Φ μs v : (|==> Φ v μs) -∗ ABWP of_val v @ μs [{ Φ }].
Proof. intros. by rewrite -abwp_bupd -abwp_value'. Qed.
Lemma abwp_value_fupd Φ e μs v : IntoVal e v → (|==> Φ v μs) -∗ ABWP e @ μs [{ Φ }].
Proof. intros ?. rewrite -abwp_bupd -abwp_value //. Qed.
Lemma abwp_value_inv Φ e μs v : IntoVal e v → ABWP e @ μs [{ Φ }] ==∗ Φ v μs.
Proof. intros <-. by apply abwp_value_inv'. Qed.

Lemma abwp_frame_l e μs Φ R :
  R ∗ ABWP e @ μs [{ Φ }] -∗ ABWP e @ μs [{ v; κs, R ∗ Φ v κs}].
Proof. iIntros "[? H]". iApply (abwp_strong_mono with "H"); auto with iFrame. Qed.
Lemma abwp_frame_r e μs Φ R : ABWP e @ μs [{ Φ }] ∗ R -∗ ABWP e @ μs [{ v ; κs, Φ v κs ∗ R }].
Proof. iIntros "[H ?]". iApply (abwp_strong_mono with "H"); auto with iFrame. Qed.

Lemma abwp_wand e μs Φ Ψ :
  ABWP e @ μs [{ Φ }] -∗ (∀ v κs, Φ v κs -∗ Ψ v κs) -∗ ABWP e @ μs [{ Ψ }].
Proof.
  iIntros "H HΦ". iApply (abwp_strong_mono with "H"); auto.
  iIntros (??) "?". by iApply "HΦ".
Qed.
Lemma abwp_wand_l e μs Φ Ψ :
  (∀ v κs, Φ v κs -∗ Ψ v κs) ∗ ABWP e @ μs [{ Φ }] -∗ ABWP e @ μs [{ Ψ }].
Proof. iIntros "[H Hwp]". iApply (abwp_wand with "Hwp H"). Qed.
Lemma abwp_wand_r e μs Φ Ψ :
  ABWP e @ μs [{ Φ }] ∗ (∀ v κs, Φ v κs -∗ Ψ v κs) -∗ ABWP e @ μs [{ Ψ }].
Proof. iIntros "[Hwp H]". iApply (abwp_wand with "Hwp H"). Qed.
End abwp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{irisG Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → (list (observation Λ)) → iProp Σ.
  Implicit Types μs κs : list (observation Λ).


  Global Instance frame_abwp p e μs R Φ Ψ :
    (∀ v κs, Frame p R (Φ v κs) (Ψ v κs)) →
    Frame p R (ABWP e @ μs [{ Φ }]) (ABWP e @ μs [{ Ψ }]).
  Proof. rewrite /Frame=> HR. rewrite abwp_frame_l. apply abwp_mono, HR. Qed.

  Global Instance elim_modal_bupd_abwp p e μs P Φ :
    ElimModal True p false (|==> P) P (ABWP e @ μs [{ Φ }]) (ABWP e @ μs [{ Φ }]).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim /=
            bupd_frame_r wand_elim_r bupd_abwp.
  Qed.

  Global Instance add_modal_bupd_abwp e μs P Φ :
    AddModal (|==> P) P (ABWP e @ μs [{ Φ }]).
  Proof. by rewrite /AddModal bupd_frame_r wand_elim_r bupd_abwp. Qed.
End proofmode_classes.


(** For atomic block weakest preconditions we only prove the following
instead of adequacy. These are enough for deriving WP's for atomic
blocks based on the ABWP's of their bodies. *)

From atomic_block.program_logic Require Import atomic_ectx_language.

Section abwp_steps_atomically.
  Context {Λ : atomicectxLanguage}.
  Context `{irisG Λ Σ}.
  Implicit Types e : expr Λ.

  Lemma abwp_steps_atomically Φ e σ1 μs κs n :
    state_interp σ1 κs n ∗ ABWP e @ μs [{ Φ }] ==∗
    ∃ v κs' σ2, ⌜steps_atomically e σ1 κs' (of_val v) σ2⌝.
  Proof.
    iIntros "[Hsi Hab]". iRevert (σ1 κs n) "Hsi".  iRevert (e μs Φ) "Hab".
    iApply abwp_ind.
    iIntros "!#" (e μs Φ) "IH".
    iIntros (σ1 κs n) "Hsi"; simpl.
    rewrite /abwp_pre /=.
    destruct (to_val e) as [v|] eqn:He1.
    { iModIntro. iExists _, _, _; iPureIntro.
      econstructor; eauto using to_of_val. }
    iMod ("IH" with "[$]") as "[Hrd IH]".
    iDestruct "Hrd" as %(?&?&?&?&Hrd); simpl in *.
    iMod ("IH" with "[]") as "[% [Hsi IH]]"; eauto; simplify_eq.
    iMod ("IH" with "[$]") as (???) "%".
    iModIntro. iExists _, _, _; iPureIntro.
    econstructor 2; eauto.
  Qed.

  Lemma abwp_steps_atomically_useful E E' Φ e σ1 μs κs n :
    ▷ state_interp σ1 κs n -∗
    (|={E, E'}=> ▷ ABWP e @ μs [{ v ; κs, |={E', E}=> Φ v κs}]) ={E}=∗
    (∃ v κs' σ2, ⌜steps_atomically e σ1 κs' (of_val v) σ2⌝) ∗
                 ▷ state_interp σ1 κs n ∗
                 (|={E, E'}=> ▷ ABWP e @ μs [{ v ; κs, |={E', E}=> Φ v κs}]).
  Proof.
    iIntros "Hsi Hab".
    iApply (fupd_plain_keep_l); iFrame.
    iIntros "[Hsi Hab]".
    iApply fupd_plain_mask. iMod "Hab".
    iAssert (▷ ∃ v κs' σ2, ⌜steps_atomically e σ1 κs' (of_val v) σ2⌝)%I
      as "#>HSA"; last done.
    iNext. iMod (abwp_steps_atomically with "[$]"); iFrame.
  Qed.

  Lemma abwp_steps_atomically_post Φ e σ1 μs κs n v κs' σ2:
    state_interp σ1 κs n -∗
    ⌜steps_atomically e σ1 κs' (of_val v) σ2⌝ -∗
    ABWP e @ μs [{ Φ }] ==∗ state_interp σ2 κs n ∗ Φ v (μs ++ κs').
  Proof.
    iIntros "Hsi Hsa Hab". iDestruct "Hsa" as %Hsa.
    remember (of_val v) as e2.
    iInduction Hsa as [?????? ?%of_to_val ?%of_to_val|?????????? Hpstp] "IH"
     forall (μs); simpl in *; simplify_eq.
    { rewrite abwp_value_inv' app_nil_r. by iMod "Hab"; iFrame. }
    rewrite [ABWP e1 @ _ [{_}]%I]abwp_unfold /abwp_pre /=.
    destruct (to_val e1) as [w|] eqn:He1.
    { apply val_prim_stuck in Hpstp; simplify_eq. }
    iMod ("Hab" with "[$]") as "[_ Hab]".
    iMod ("Hab" with "[]") as "(_&Hsi&Hab)"; eauto.
    rewrite assoc.
    iMod ("IH" with "[] [$] [$]") as "[$ HΦ]"; trivial.
  Qed.

End abwp_steps_atomically.
