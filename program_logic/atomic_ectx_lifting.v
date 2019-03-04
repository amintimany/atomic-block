(** Some derived lemmas for ectx-based languages *)
From iris.program_logic Require Export weakestpre lifting.
From atomic_block.program_logic Require Export atomic_ectx_language.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section wp.
Context {Λ : atomicectxLanguage} `{irisG Λ Σ} {Hinh : Inhabited (state Λ)}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Hint Resolve head_prim_reducible head_reducible_prim_step : core.
Hint Resolve (reducible_not_val _ inhabitant) : core.
Hint Resolve head_stuck_stuck : core.

(* NAB stands for non-atomic-block *)

Lemma wp_lift_head_step_fupd {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κ κs n, state_interp σ1 (κ ++ κs) n ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={∅,∅,E}▷=∗
      state_interp σ2 κs (length efs + n) ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd=>//. iIntros (σ1 κ κs Qs) "Hσ".
  iMod ("H" with "Hσ") as "[% H]"; iModIntro.
  iSplit; first by destruct s; eauto. iIntros (e2 σ2 efs ?).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_head_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κ κs n, state_interp σ1 (κ ++ κs) n ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
      state_interp σ2 κs (length efs + n) ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_head_step_fupd; [done|]. iIntros (????) "?".
  iMod ("H" with "[$]") as "[$ H]". iIntros "!>" (e2 σ2 efs ?) "!> !>". by iApply "H".
Qed.

Lemma wp_lift_NAB_head_stuck E Φ e :
  atomic_block_of e = None →
  to_val e = None →
  sub_redexes_are_values e →
  (∀ σ κs n, state_interp σ κs n ={E,∅}=∗ ⌜head_stuck e σ⌝)
  ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (???) "H". iApply wp_lift_stuck; first done.
  iIntros (σ κs n) "Hσ". iMod ("H" with "Hσ") as "%". by auto.
Qed.

Lemma wp_lift_pure_head_stuck E Φ e :
  atomic_block_of e = None →
  to_val e = None →
  sub_redexes_are_values e →
  (∀ σ, head_stuck e σ) →
  WP e @ E ?{{ Φ }}%I.
Proof using Hinh.
  iIntros (??? Hstuck). iApply wp_lift_NAB_head_stuck; [done|done|done|].
  iIntros (σ κs n) "_". iMod (fupd_intro_mask' E ∅) as "_"; first set_solver.
  by auto.
Qed.

Lemma wp_lift_atomic_head_step_fupd {s E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κ κs n, state_interp σ1 (κ ++ κs) n ={E1}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E1,E2}▷=∗
      state_interp σ2 κs (length efs + n) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (σ1 κ κs Qs) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by destruct s; auto. iIntros (e2 σ2 efs Hstep).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_head_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κ κs n, state_interp σ1 (κ ++ κs) n ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 κs (length efs + n) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step; eauto.
  iIntros (σ1 κ κs Qs) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by destruct s; auto. iNext. iIntros (e2 σ2 efs Hstep).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_head_step_no_fork_fupd {s E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κ κs n, state_interp σ1 (κ ++ κs) n ={E1}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E1,E2}▷=∗
      ⌜efs = []⌝ ∗ state_interp σ2 κs n ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_head_step_fupd; [done|].
  iIntros (σ1 κ κs Qs) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
  iIntros (v2 σ2 efs Hstep).
  iMod ("H" $! v2 σ2 efs with "[# //]") as "H".
  iIntros "!> !>". iMod "H" as "(-> & ? & ?) /=". by iFrame.
Qed.

Lemma wp_lift_atomic_head_step_no_fork {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 κ κs n, state_interp σ1 (κ ++ κs) n ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      ⌜efs = []⌝ ∗ state_interp σ2 κs n ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_head_step; eauto.
  iIntros (σ1 κ κs Qs) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
  iNext; iIntros (v2 σ2 efs Hstep).
  iMod ("H" $! v2 σ2 efs with "[//]") as "(-> & ? & ?) /=". by iFrame.
Qed.

Lemma wp_lift_pure_det_head_step_no_fork {s E E' Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 κ e2' σ2 efs',
    head_step e1 σ1 κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E,E'}▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(wp_lift_pure_det_step_no_fork e1 e2); eauto.
  destruct s; by auto.
Qed.

Lemma wp_lift_pure_det_head_step_no_fork' {s E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 κ e2' σ2 efs',
    head_step e1 σ1 κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  ▷ WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -[(WP e1 @ s; _ {{ _ }})%I]wp_lift_pure_det_head_step_no_fork //.
  rewrite -step_fupd_intro //.
Qed.

Hint Resolve atomically_reducible_reducible.

Lemma wp_lift_atomic_block_stuck E Φ e ab:
  atomic_block_of e = Some ab →
  (∀ σ κs n, state_interp σ κs n ={E,∅}=∗ ⌜atomically_irreducible ab σ⌝)
  ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply wp_lift_stuck; first by simpl; eauto using atomic_block_not_val.
  iIntros (σ κs n) "Hσ". iMod ("H" with "Hσ") as "%".
  by eauto using atomically_irreducible_stuck.
Qed.

Lemma wp_lift_pure_atomic_block_stuck E Φ e ab :
  atomic_block_of e = Some ab →
  (∀ σ, atomically_irreducible ab σ) →
  WP e @ E ?{{ Φ }}%I.
Proof using Hinh.
  iIntros (? Hstuck). iApply wp_lift_atomic_block_stuck; first done.
  iIntros (σ κs n) "_". iMod (fupd_intro_mask' E ∅) as "_"; first set_solver.
  by auto.
Qed.

Lemma wp_lift_atomic_block_fupd {s E1 E2 Φ} e1 ab :
  atomic_block_of e1 = Some ab →
  (∀ σ1 κ κs n, state_interp σ1 (κ ++ κs) n ={E1}=∗
    ⌜atomically_reducible ab σ1⌝ ∗
    ∀ e2 σ2, ⌜steps_atomically ab σ1 κ e2 σ2⌝ ={E1,E2}▷=∗
      state_interp σ2 κs n ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply wp_lift_atomic_step_fupd; first by eapply atomic_block_not_val.
  iIntros (σ1 κ κs Qs) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by destruct s; eauto. iIntros (e2 σ2 efs Hstep).
  eapply atomic_block_prim_step in Hstep; eauto.
  destruct Hstep as [? ?]; simplify_eq.
  iMod ("H" with "[]") as "H"; eauto.
  iModIntro; iNext.
  iMod "H" as "[$ $]"; eauto.
Qed.

Lemma wp_lift_atomic_block {s E Φ} e1 ab :
  atomic_block_of e1 = Some ab →
  (∀ σ1 κ κs n, state_interp σ1 (κ ++ κs) n ={E}=∗
    ⌜atomically_reducible ab σ1⌝ ∗
    ▷ ∀ e2 σ2, ⌜steps_atomically ab σ1 κ e2 σ2⌝ ={E}=∗
      state_interp σ2 κs n ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply wp_lift_atomic_step; first by eapply atomic_block_not_val.
  iIntros (σ1 κ κs Qs) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by destruct s; eauto. iNext. iIntros (e2 σ2 efs Hstep).
  eapply atomic_block_prim_step in Hstep; eauto.
  destruct Hstep as [? ?]; simplify_eq.
  iMod ("H" with "[]") as "[$ $]"; eauto.
Qed.

End wp.
