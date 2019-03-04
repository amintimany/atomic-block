From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From iris.bi Require Import fixpoint big_op.
Set Default Proof Using "Type".
Import uPred.

(* Type class and Notation for atomic block WP's *)

Class ABwp (Λ : language) (PROP : Type) :=
  abwp : coPset → expr Λ → list (observation Λ) →
         (val Λ → list (observation Λ) → PROP) → PROP.
Arguments twp {_ _ _ _} _ _%E _ _%I.
Instance: Params (@twp) 6 := {}.

(** Notations for atomic block WP's *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'ABWP' e @ μs ; E [{ Φ } ]" := (abwp E e%E μs Φ)
  (at level 20, e, μs, Φ at level 200, only parsing) : bi_scope.
Notation "'ABWP' e @ E [{ Φ } ]" := (abwp E e%E [] Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'ABWP' e @ μs [{ Φ } ]" := (abwp ⊤ e%E μs Φ)
  (at level 20, e, μs, Φ at level 200, only parsing) : bi_scope.
Notation "'ABWP' e [{ Φ } ]" := (abwp ⊤ e%E [] Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder.  The indentation for the inner format block is chosen
such that *if* one has a single-character mask (e.g. [E]), the second line
should align with the binder(s) on the first line. *)
Notation "'ABWP' e @ μs ; E [{ v ; κs , Q } ]" := (abwp E e%E μs (λ v κs, Q))
  (at level 20, e, μs, Q at level 200,
   format "'[' 'ABWP'  e  '/' '[          ' @  μs ;  E  [{  v ; κs ,  Q  } ] ']' ']'") : bi_scope.
Notation "'ABWP' e @ E [{ v ; κs , Q } ]" := (abwp E e%E [] (λ v κs, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'ABWP'  e  '/' '[       ' @  E  [{  v ; κs ,  Q  } ] ']' ']'") : bi_scope.
Notation "'ABWP' e [{ v ; κs , Q } ]" := (abwp ⊤ e%E [] (λ v κs, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'ABWP'  e  '/' '[   ' [{  v ; κs ,  Q  } ] ']' ']'") : bi_scope.
Notation "'ABWP' e [{ v ; κs , Q } ]" := (abwp ⊤ e%E [] (λ v κs, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'ABWP'  e  '/' '[    ' [{  v ; κs ,  Q  } ] ']' ']'") : bi_scope.

Definition abwp_pre `{irisG Λ Σ}
           (wp : coPset → expr Λ → list (observation Λ) →
                 (val Λ → list (observation Λ) → iProp Σ) → iProp Σ) :
  coPset → expr Λ → list (observation Λ) →
  (val Λ → list (observation Λ) → iProp Σ) → iProp Σ := λ E e1 μs Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v μs
  | None => ∀ σ1 κs n,
     state_interp σ1 κs n ={E,∅}=∗ ⌜reducible e1 σ1⌝ ∗
       ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
         ⌜efs = []⌝ ∗
         state_interp σ2 κs n ∗ wp E e2 (μs ++ κ) Φ
  end%I.

Lemma abwp_pre_mono `{irisG Λ Σ}
    (wp1 wp2 : coPset → expr Λ → list (observation Λ) →
               (val Λ → list (observation Λ) → iProp Σ) → iProp Σ) :
  ((□ ∀ E e μs Φ, wp1 E e μs Φ -∗ wp2 E e μs Φ) →
  ∀ E e μs Φ, abwp_pre wp1 E e μs Φ -∗ abwp_pre wp2 E e μs Φ)%I.
Proof.
  iIntros "#H"; iIntros (E e1 μs Φ) "Hwp". rewrite /abwp_pre.
  destruct (to_val e1) as [v|]; first done.
  iIntros (σ1 κs n) "Hσ". iMod ("Hwp" with "Hσ") as "($ & Hwp)"; iModIntro.
  iIntros (κ e2 σ2 efs) "Hstep".
  iMod ("Hwp" with "Hstep") as (?) "(Hσ & Hwp)".
  iModIntro. iFrame "Hσ"; iSplit; first done. by iApply "H".
Qed.

(* Uncurry [abwp_pre] and equip its type with an OFE structure *)
Definition abwp_pre' `{irisG Λ Σ} :
  (prodC (prodC (prodC (leibnizC coPset) (exprC Λ))
                (leibnizC (list (observation Λ))))
         (val Λ -c> (leibnizC (list (observation Λ))) -c> iProp Σ) → iProp Σ) →
  (prodC (prodC (prodC (leibnizC coPset) (exprC Λ))
                (leibnizC (list (observation Λ))))
         (val Λ -c> (leibnizC (list (observation Λ))) -c> iProp Σ) → iProp Σ)
  := curry4 ∘ abwp_pre ∘ uncurry4.

Local Instance abwp_pre_mono' `{irisG Λ Σ} : BiMonoPred (abwp_pre').
Proof.
  constructor.
  - iIntros (wp1 wp2) "#H"; iIntros ([[[E e1] μs] Φ]); iRevert (E e1 μs Φ).
    iApply abwp_pre_mono. iIntros "!#" (E e μs Φ). iApply ("H" $! (E,e, μs,Φ)).
  - intros wp Hwp n [[[E1 e1] μs] Φ1] [[[E2 e2] μs2] Φ2]
      [[[?%leibniz_equiv ?%leibniz_equiv] ?%leibniz_equiv] HPhi]; simplify_eq/=.
    rewrite /uncurry4 /abwp_pre. do 23 (f_equiv || apply HPhi || done).
    by apply pair_ne.
Qed.

Definition abwp_def `{irisG Λ Σ} (E : coPset)
    (e : expr Λ) (μs : list (observation Λ))
    (Φ : val Λ → (list (observation Λ)) → iProp Σ) :
  iProp Σ := bi_least_fixpoint (abwp_pre') (E,e,μs,Φ).
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
Lemma abwp_unfold E e μs Φ : ABWP e @ μs; E [{ Φ }] ⊣⊢ abwp_pre abwp E e μs Φ.
Proof. by rewrite abwp_eq /abwp_def least_fixpoint_unfold. Qed.
Lemma abwp_ind Ψ :
  (∀ n E e μs, Proper (pointwise_relation _  (pointwise_relation _ (dist n)) ==> dist n) (Ψ E e μs)) →
  (□ (∀ e μs E Φ,
         abwp_pre (λ E e μs Φ, Ψ E e μs Φ ∧
                               ABWP e @ μs; E [{ Φ }]) E e μs Φ -∗ Ψ E e μs Φ) →
  ∀ e μs E Φ, ABWP e @ μs; E [{ Φ }] -∗ Ψ E e μs Φ)%I.
Proof.
  iIntros (HΨ). iIntros "#IH" (e μs E Φ) "H". rewrite abwp_eq.
  set (Ψ' := curry4 Ψ :
    (prodC (prodC (prodC (leibnizC coPset) (exprC Λ))
                (leibnizC (list (observation Λ))))
         (val Λ -c> (leibnizC (list (observation Λ))) -c> iProp Σ) → iProp Σ)).
  assert (NonExpansive Ψ').
  { intros n [[[E1 e1] μs1] Φ1] [[[E2 e2] μs2] Φ2]
      [[[?%leibniz_equiv ?%leibniz_equiv] ?%leibniz_equiv] ?]; simplify_eq/=.
      by apply HΨ. }
  iApply (least_fixpoint_strong_ind _ Ψ' with "[] H").
  iIntros "!#" ([[[??]?] ?]) "H". by iApply "IH".
Qed.

Global Instance abwp_ne E e μs n :
  Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==> dist n)
         (abwp (PROP:=iProp Σ) E e μs).
Proof.
  intros Φ1 Φ2 HΦ. rewrite !abwp_eq. by apply (least_fixpoint_ne _), pair_ne, HΦ.
Qed.
Global Instance abwp_proper E e μs :
  Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (≡))
         (abwp (PROP:=iProp Σ) E e μs).
Proof.
  intros Φ Φ' HPhi; apply equiv_dist=>n; apply abwp_ne=>v μs'; apply equiv_dist.
  apply HPhi.
Qed.

Lemma abwp_value' E Φ v μs : Φ v μs -∗ ABWP of_val v @ μs; E [{ Φ }].
Proof. iIntros "HΦ". rewrite abwp_unfold /abwp_pre to_of_val. auto. Qed.
Lemma abwp_value_inv' E Φ v μs : ABWP of_val v @ μs; E [{ Φ }] ={E}=∗ Φ v μs.
Proof. by rewrite abwp_unfold /abwp_pre to_of_val. Qed.

Lemma abwp_strong_mono E1 E2 e μs Φ Ψ :
  E1 ⊆ E2 →
  ABWP e @ μs; E1 [{ Φ }] -∗ (∀ v κs, Φ v κs ={E2}=∗ Ψ v κs) -∗ ABWP e @ μs; E2 [{ Ψ }].
Proof.
  iIntros (HE) "H HΦ". iRevert (E2 Ψ HE) "HΦ"; iRevert (e μs E1 Φ) "H".
  iApply abwp_ind; first solve_proper.
  iIntros "!#" (e μs E1 Φ) "IH"; iIntros (E2 Ψ HE) "HΦ".
  rewrite !abwp_unfold /abwp_pre. destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1 κs n) "Hσ". iMod (fupd_intro_mask' E2 E1) as "Hclose"; first done.
  iMod ("IH" with "[$]") as "[% IH]".
  iModIntro; iSplit; first done. iIntros (κ e2 σ2 efs Hstep).
  iMod ("IH" with "[//]") as (?) "(Hσ & IH)"; auto.
  iMod "Hclose" as "_"; iModIntro.
  iFrame "Hσ". iSplit; first done.
  iDestruct "IH" as "[IH _]". iApply ("IH" with "[//] HΦ").
Qed.

Lemma fupd_abwp E e μs Φ : (|={E}=> ABWP e @ μs; E [{ Φ }]) -∗ ABWP e @ μs; E [{ Φ }].
Proof.
  rewrite abwp_unfold /abwp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 κs n) "Hσ1". iMod "H". by iApply "H".
Qed.
Lemma abwp_fupd E e μs Φ :
  ABWP e @ μs; E [{ v; κs, |={E}=> Φ v κs }] -∗ ABWP e @ μs; E [{ Φ }].
Proof. iIntros "H". iApply (abwp_strong_mono with "H"); auto. Qed.

Lemma abwp_atomic E1 E2 e μs Φ `{!Atomic StronglyAtomic e} :
  (|={E1,E2}=> ABWP e @ μs; E2 [{ v; κs, |={E2,E1}=> Φ v κs }])
    -∗ ABWP e @ μs; E1 [{ Φ }].
Proof.
  iIntros "H". rewrite !abwp_unfold /abwp_pre /=.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1 κs n) "Hσ". iMod "H". iMod ("H" $! σ1 with "Hσ") as "[$ H]".
  iModIntro. iIntros (κ e2 σ2 efs Hstep).
  iMod ("H" with "[//]") as (?) "(Hσ & H)"; simplify_eq.
  rewrite !abwp_unfold /abwp_pre. destruct (to_val e2) as [v2|] eqn:He2.
  - iDestruct "H" as ">> $". by iFrame.
  - iMod ("H" with "[$]") as "[H _]".
    iDestruct "H" as %(? & ? & ? & ? & ?).
    by edestruct (atomic _ _ _ _ _ Hstep); simplify_eq.
Qed.

Lemma abwp_bind K `{!LanguageCtx K} μs E e Φ :
  ABWP e @ μs; E [{ v ; κs, ABWP K (of_val v) @ κs; E [{ Φ }] }]
                 -∗ ABWP K e @ μs; E [{ Φ }].
Proof.
  revert Φ. cut (∀ Φ', ABWP e @ μs; E [{ Φ' }] -∗ ∀ Φ,
    (∀ v κs, Φ' v κs -∗ ABWP K (of_val v) @ κs; E [{ Φ }])
      -∗ ABWP K e @ μs; E [{ Φ }]).
  { iIntros (help Φ) "H". iApply (help with "H"); auto. }
  iIntros (Φ') "H". iRevert (e μs E Φ') "H". iApply abwp_ind; first solve_proper.
  iIntros "!#" (e μs E1 Φ') "IH". iIntros (Φ) "HΦ".
  rewrite /abwp_pre. destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iApply fupd_abwp. by iApply "HΦ". }
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

Lemma abwp_bind_inv K `{!LanguageCtx K} μs E e Φ :
  ABWP K e @ μs; E [{ Φ }] -∗ ABWP e @ μs; E [{ v; κs, ABWP K (of_val v) @ κs; E [{ Φ }] }].
Proof.
  iIntros "H". remember (K e) as e' eqn:He'.
  iRevert (e He'). iRevert (e' μs E Φ) "H". iApply abwp_ind; first solve_proper.
  iIntros "!#" (e' μs E1 Φ) "IH". iIntros (e ->).
  rewrite !abwp_unfold {2}/abwp_pre. destruct (to_val e) as [v|] eqn:He.
  { iModIntro. apply of_to_val in He as <-. rewrite !abwp_unfold.
    iApply (abwp_pre_mono with "[] IH"). by iIntros "!#" (E e μs' Φ') "[_ ?]". }
  rewrite /abwp_pre fill_not_val //.
  iIntros (σ1 κs n) "Hσ". iMod ("IH" with "[$]") as "[% IH]". iModIntro; iSplit.
  { eauto using reducible_fill. }
  iIntros (κ e2 σ2 efs Hstep).
  iMod ("IH" $! κ (K e2) σ2 efs with "[]") as (?) "(Hσ & IH)"; eauto using fill_step.
  iModIntro. iFrame "Hσ". iSplit; first done.
  iDestruct "IH" as "[IH _]". by iApply "IH".
Qed.

(** * Derived rules *)
Lemma abwp_mono E e μs Φ Ψ :
  (∀ v κs, Φ v κs -∗ Ψ v κs) → ABWP e @ μs; E [{ Φ }] -∗ ABWP e @ μs; E [{ Ψ }].
Proof.
  iIntros (HΦ) "H"; iApply (abwp_strong_mono with "H"); auto.
  iIntros (v κs) "?". by iApply HΦ.
Qed.
Lemma abwp_mask_mono E1 E2 e μs Φ :
  E1 ⊆ E2 → ABWP e @ μs; E1 [{ Φ }] -∗ ABWP e @ μs; E2 [{ Φ }].
Proof. iIntros (?) "H"; iApply (abwp_strong_mono with "H"); auto. Qed.
Global Instance abwp_mono' E e μs:
  Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (⊢))
         (abwp (PROP:=iProp Σ) E e μs).
Proof. by intros Φ Φ' ?; apply abwp_mono. Qed.

Lemma abwp_value E Φ e μs v : IntoVal e v → Φ v μs -∗ ABWP e @ μs; E [{ Φ }].
Proof. intros <-. by apply abwp_value'. Qed.
Lemma abwp_value_fupd' E Φ μs v : (|={E}=> Φ v μs) -∗ ABWP of_val v @ μs; E [{ Φ }].
Proof. intros. by rewrite -abwp_fupd -abwp_value'. Qed.
Lemma abwp_value_fupd E Φ e μs v : IntoVal e v → (|={E}=> Φ v μs) -∗ ABWP e @ μs; E [{ Φ }].
Proof. intros ?. rewrite -abwp_fupd -abwp_value //. Qed.
Lemma abwp_value_inv E Φ e μs v : IntoVal e v → ABWP e @ μs; E [{ Φ }] ={E}=∗ Φ v μs.
Proof. intros <-. by apply abwp_value_inv'. Qed.

Lemma abwp_frame_l E e μs Φ R :
  R ∗ ABWP e @ μs; E [{ Φ }] -∗ ABWP e @ μs; E [{ v; κs, R ∗ Φ v κs}].
Proof. iIntros "[? H]". iApply (abwp_strong_mono with "H"); auto with iFrame. Qed.
Lemma abwp_frame_r E e μs Φ R : ABWP e @ μs; E [{ Φ }] ∗ R -∗ ABWP e @ μs; E [{ v ; κs, Φ v κs ∗ R }].
Proof. iIntros "[H ?]". iApply (abwp_strong_mono with "H"); auto with iFrame. Qed.

Lemma abwp_wand E e μs Φ Ψ :
  ABWP e @ μs; E [{ Φ }] -∗ (∀ v κs, Φ v κs -∗ Ψ v κs) -∗ ABWP e @ μs; E [{ Ψ }].
Proof.
  iIntros "H HΦ". iApply (abwp_strong_mono with "H"); auto.
  iIntros (??) "?". by iApply "HΦ".
Qed.
Lemma abwp_wand_l E e μs Φ Ψ :
  (∀ v κs, Φ v κs -∗ Ψ v κs) ∗ ABWP e @ μs; E [{ Φ }] -∗ ABWP e @ μs; E [{ Ψ }].
Proof. iIntros "[H Hwp]". iApply (abwp_wand with "Hwp H"). Qed.
Lemma abwp_wand_r E e μs Φ Ψ :
  ABWP e @ μs; E [{ Φ }] ∗ (∀ v κs, Φ v κs -∗ Ψ v κs) -∗ ABWP e @ μs; E [{ Ψ }].
Proof. iIntros "[Hwp H]". iApply (abwp_wand with "Hwp H"). Qed.
End abwp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{irisG Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → (list (observation Λ)) → iProp Σ.
  Implicit Types μs κs : list (observation Λ).


  Global Instance frame_abwp p E e μs R Φ Ψ :
    (∀ v κs, Frame p R (Φ v κs) (Ψ v κs)) →
    Frame p R (ABWP e @ μs; E [{ Φ }]) (ABWP e @ μs; E [{ Ψ }]).
  Proof. rewrite /Frame=> HR. rewrite abwp_frame_l. apply abwp_mono, HR. Qed.

  Global Instance is_except_0_wp E e μs Φ : IsExcept0 (ABWP e @ μs; E [{ Φ }]).
  Proof. by rewrite /IsExcept0 -{2}fupd_abwp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_abwp p E e μs P Φ :
    ElimModal True p false (|==> P) P (ABWP e @ μs; E [{ Φ }]) (ABWP e @ μs; E [{ Φ }]).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_abwp.
  Qed.

  Global Instance elim_modal_fupd_abwp p E e μs P Φ :
    ElimModal True p false (|={E}=> P) P (ABWP e @ μs; E [{ Φ }]) (ABWP e @ μs; E [{ Φ }]).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_abwp.
  Qed.

  Global Instance elim_modal_fupd_abwp_atomic p E1 E2 e μs P Φ :
    Atomic StronglyAtomic e →
    ElimModal True p false (|={E1,E2}=> P) P
            (ABWP e @ μs; E1 [{ Φ }]) (ABWP e @ μs; E2 [{ v;κs, |={E2,E1}=> Φ v κs}])%I.
  Proof.
    intros. by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r abwp_atomic.
  Qed.

  Global Instance add_modal_fupd_abwp E e μs P Φ :
    AddModal (|={E}=> P) P (ABWP e @ μs; E [{ Φ }]).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_abwp. Qed.
End proofmode_classes.


(** For atomic block weakest preconditions we only prove the following
instead of adequacy. These are enough for deriving WP's for atomic
blocks based on the ABWP's of their bodies. *)

From atomic_block.program_logic Require Import atomic_ectx_language.

Section abwp_steps_atomically.
  Context {Λ : atomicectxLanguage}.
  Context `{irisG Λ Σ}.
  Implicit Types e : expr Λ.

  Lemma abwp_steps_atomically E Φ e σ1 μs κs n :
    state_interp σ1 κs n ∗ ABWP e @ μs; E [{ Φ }] ={E}=∗
    ∃ v κs' σ2, ⌜steps_atomically e σ1 κs' (of_val v) σ2⌝.
  Proof.
    iIntros "[Hsi Hab]". iRevert (σ1 κs n) "Hsi".  iRevert (e μs E Φ) "Hab".
    iApply abwp_ind.
    iIntros "!#" (e μs E Φ) "IH".
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
    state_interp σ1 κs n -∗
    (|={E, E'}=> ABWP e @ μs; E' [{ v ; κs, |={E', E}=> Φ v κs}]) ={E}=∗
    (∃ v κs' σ2, ⌜steps_atomically e σ1 κs' (of_val v) σ2⌝) ∗
                 state_interp σ1 κs n ∗
                 (|={E, E'}=> ABWP e @ μs; E' [{ v ; κs, |={E', E}=> Φ v κs}]).
  Proof.
    iIntros "Hsi Hab".
    iApply (fupd_plain_keep_l); iFrame.
    iIntros "[Hsi Hab]".
    iApply fupd_plain_mask. iMod "Hab".
    iApply abwp_steps_atomically; iFrame.
  Qed.

  Lemma abwp_steps_atomically_post E Φ e σ1 μs κs n v κs' σ2:
    state_interp σ1 κs n -∗
    ⌜steps_atomically e σ1 κs' (of_val v) σ2⌝ -∗
    ABWP e @ μs; E [{ Φ }] ={E}=∗ state_interp σ2 κs n ∗ Φ v (μs ++ κs').
  Proof.
    iIntros "Hsi Hsa Hab". iDestruct "Hsa" as %Hsa.
    remember (of_val v) as e2.
    iInduction Hsa as [?????? ?%of_to_val ?%of_to_val|?????????? Hpstp] "IH"
     forall (μs); simpl in *; simplify_eq.
    { rewrite abwp_value_inv' app_nil_r. by iMod "Hab"; iFrame. }
    rewrite [ABWP e1 @ _; _ [{_}]%I]abwp_unfold /abwp_pre /=.
    destruct (to_val e1) as [w|] eqn:He1.
    { apply val_prim_stuck in Hpstp; simplify_eq. }
    iMod ("Hab" with "[$]") as "[_ Hab]".
    iMod ("Hab" with "[]") as "(_&Hsi&Hab)"; eauto.
    rewrite assoc.
    iMod ("IH" with "[] [$] [$]") as "[$ HΦ]"; trivial.
  Qed.

End abwp_steps_atomically.
