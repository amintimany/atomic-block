(** Some derived lemmas for ectx-based languages *)
From atomic_block.program_logic Require Export total_atomic_weakestpre
     atomic_ectx_language total_atomic_lifting atomic_ectx_lifting.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section wp.
Context {Λ : atomicectxLanguage} `{irisG Λ Σ} {Hinh : Inhabited (state Λ)}.
Implicit Types P : iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types Φ : val Λ → (list (observation Λ)) → iProp Σ.
Implicit Types μs κs : list (observation Λ).

Hint Resolve head_prim_reducible head_reducible_prim_step : core.

Lemma abwp_lift_head_step {E Φ μs} e1 :
  to_val e1 = None →
  (∀ σ1 κs n, state_interp σ1 κs n ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ κ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
      ⌜efs = []⌝ ∗
      state_interp σ2 κs n ∗ ABWP e2 @ (μs ++ κ); E [{ Φ }])
  ⊢ ABWP e1 @ μs; E [{ Φ }].
Proof.
  iIntros (?) "H".
  iApply (abwp_lift_step E)=>//. iIntros (σ1 κs n) "Hσ".
  iMod ("H" $! σ1 with "Hσ") as "[% H]"; iModIntro.
  iSplit; first by eauto. iIntros (κ e2 σ2 efs Hstep).
  iApply "H". by eauto.
Qed.

Lemma abwp_lift_pure_head_step {E Φ μs} e1 :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 κ e2 σ2 efs, head_step e1 σ1 κ e2 σ2 efs → σ2 = σ1 ∧ efs = []) →
  (|={E}=> ∀ κ e2 efs σ, ⌜head_step e1 σ κ e2 σ efs⌝ → ABWP e2 @ (μs ++ κ); E [{ Φ }] )
  ⊢ ABWP e1 @ μs; E [{ Φ }].
Proof using Hinh.
  iIntros (??) ">H". iApply abwp_lift_pure_step; eauto.
  iIntros "!>" (?????). iApply "H"; eauto.
Qed.

Lemma abwp_lift_atomic_head_step {E Φ μs} e1 :
  to_val e1 = None →
  (∀ σ1 κs n, state_interp σ1 κs n ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ κ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      ⌜efs = []⌝ ∗
      state_interp σ2 κs n ∗ from_option (λ v, Φ v (μs ++ κ)) False (to_val e2))
  ⊢ ABWP e1 @ μs; E [{ Φ }].
Proof.
  iIntros (?) "H". iApply abwp_lift_atomic_step; eauto.
  iIntros (σ1 κs n) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first eauto. iIntros (κ e2 σ2 efs Hstep). iApply "H"; eauto.
Qed.

Lemma abwp_lift_pure_det_head_step {E Φ μs} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 κ e2' σ2 efs',
    head_step e1 σ1 κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  ABWP e2 @ μs; E [{ Φ }] ⊢ ABWP e1 @ μs; E [{ Φ }].
Proof using Hinh.
  intros. rewrite -(abwp_lift_pure_det_step e1 e2); eauto.
  rewrite app_nil_r; eauto.
Qed.

(**

Ideally we want the premises to only hold later, i.e., the lemma below
instead of the following lemma in the code:

Lemma wp_atomic_block_fupd {s E1 E2 Ψ Φ} e1 ab :
  atomic_block_of e1 = Some ab →
  (|={E1, E2}=> ▷ ABWP ab @ []; E2 [{v ; κ, |={E2, E1}=> Φ v κ}]) -∗
  ▷ (∀ v κ κs σ n, state_interp σ (κ ++ κs) n -∗ Φ v κ ={E1}=∗ state_interp σ κs n ∗ Ψ v) -∗
  WP e1 @ s; E1 {{ Ψ }}.

However, with the current definition of ABWP's we cannot get
 this. Alternatively, we could have defined ABWP's with basic update
 instead of fancy updates. This would give what we want above (except
 no masks would be necessary for the ABWP) but means we have no access
 to invariants inside atomic blocks. We can open any invariants that
 we want before entering the block however. That is probably nicer.
*)

Lemma wp_atomic_block_fupd {s E1 E2 Ψ Φ} e1 ab :
  atomic_block_of e1 = Some ab →
  (|={E1, E2}=> ABWP ab @ []; E2 [{v ; κ, |={E2, E1}=> Φ v κ}]) -∗
  (∀ v κ κs σ n, state_interp σ (κ ++ κs) n -∗ Φ v κ ={E1}=∗ state_interp σ κs n ∗ Ψ v) -∗
  WP e1 @ s; E1 {{ Ψ }}.
Proof.
  iIntros (Hab) "Hab Hsiupd".
  iApply wp_lift_atomic_block_fupd; first by eauto.
  iIntros (σ1 κ κs n) "Hsi".
  iMod (abwp_steps_atomically_useful with "Hsi Hab") as "(Hrd & Hsi & Hab)".
  iDestruct "Hrd" as (v κs' σ2) "%".
  iModIntro. iSplit.
  { by iPureIntro; eexists _, _, _; eauto. }
  iIntros (e2 σ3 Hstp).
  iMod "Hab". iModIntro. iNext.
  destruct (steps_atomically_always_to_val _ _ _ _ _ Hstp) as [? ?%of_to_val];
    simplify_eq; rewrite to_of_val; simpl in *.
  iMod (abwp_steps_atomically_post _ _ _ _ _ _ _ _ κ with "[Hsi] [] [Hab]")
    as "[Hsi Hpost]"; eauto.
  iMod "Hpost"; simpl.
  by iMod ("Hsiupd" with "[$] [$]") as "[$ $]".
Qed.
End wp.
