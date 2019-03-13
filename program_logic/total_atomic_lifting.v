From atomic_block.program_logic Require Export total_atomic_weakestpre.
From iris.bi Require Export big_op.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section lifting.
Context `{irisG Λ Σ}.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → (list (observation Λ)) → iProp Σ.
Implicit Types μs κs : list (observation Λ).

Lemma abwp_lift_step Φ e1 μs :
  to_val e1 = None →
  (∀ σ1 κs n, state_interp σ1 κs n ==∗
    ⌜reducible e1 σ1⌝ ∗
    ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ==∗
      ⌜efs = []⌝ ∗ state_interp σ2 κs n ∗ ABWP e2 @ (μs ++ κ) [{ Φ }])
  ⊢ ABWP e1 @ μs [{ Φ }].
Proof. by rewrite abwp_unfold /abwp_pre=> ->. Qed.

Lemma abwp_lift_pure_step `{Inhabited (state Λ)} Φ e1 μs:
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 κ e2 σ2 efs, prim_step e1 σ1 κ e2 σ2 efs → σ2 = σ1 ∧ efs = []) →
  (|==> ∀ κ e2 efs σ, ⌜prim_step e1 σ κ e2 σ efs⌝ → ABWP e2 @ (μs ++ κ) [{ Φ }])
  ⊢ ABWP e1 @ μs [{ Φ }].
Proof.
  iIntros (Hsafe Hstep) ">H". iApply abwp_lift_step.
  { eapply reducible_not_val, (Hsafe inhabitant). }
  iIntros (σ1 κs n) "Hσ".
  iModIntro; iSplit; first by iPureIntro.
  iIntros (κ e2 σ2 efs ?). destruct (Hstep σ1 κ e2 σ2 efs) as (<-&->); auto.
  iModIntro. iDestruct ("H" with "[//]") as "H". by iFrame.
Qed.

(* Atomic steps don't need any mask-changing business here, one can
   use the generic lemmas here. *)
Lemma abwp_lift_atomic_step {Φ μs} e1 :
  to_val e1 = None →
  (∀ σ1 κs n, state_interp σ1 κs n ==∗ ⌜reducible e1 σ1⌝ ∗
    ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ==∗
      ⌜efs = []⌝ ∗ state_interp σ2 κs n ∗
      from_option (λ v, Φ v (μs ++ κ)) False (to_val e2))
  ⊢ ABWP e1 @ μs [{ Φ }].
Proof.
  iIntros (?) "H".
  iApply (abwp_lift_step _ e1)=>//; iIntros (σ1 κs n) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iIntros "!>" (κ e2 σ2 efs) "%".
  iMod ("H" $! κ e2 σ2 efs with "[#]") as "($ & $ & HΦ)"; first by eauto.
  destruct (to_val e2) eqn:?; simpl in *; last by iExFalso.
  iApply abwp_value; last done. by apply of_to_val.
Qed.

Lemma abwp_lift_pure_det_step `{Inhabited (state Λ)} {Φ μs} e1 e2 κ :
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 κ' e2' σ2 efs', prim_step e1 σ1 κ' e2' σ2 efs' →
    κ' = κ ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|==> ABWP e2 @ (μs ++ κ) [{ Φ }]) ⊢ ABWP e1 @ μs [{ Φ }].
Proof.
  iIntros (? Hpuredet) ">H". iApply (abwp_lift_pure_step); try done.
  { naive_solver. }
  iIntros "!>" (κ' e' efs' σ (->&_&->&->)%Hpuredet); auto.
Qed.

Lemma abwp_pure_step `{Inhabited (state Λ)} e1 e2 μs φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  ABWP e2 @ μs [{ Φ }] ⊢ ABWP e1 @ μs [{ Φ }].
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
  iApply abwp_lift_pure_det_step;
    [auto using reducible_no_obs_reducible |naive_solver|].
  rewrite app_nil_r.
  iModIntro. by iApply "IH".
Qed.

End lifting.
