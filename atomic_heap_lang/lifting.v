From iris.algebra Require Import auth gmap.
From iris.base_logic Require Export gen_heap.
From iris.program_logic Require Export weakestpre.
From atomic_block.program_logic Require Import
     atomic_ectx_lifting total_atomic_ectx_lifting.
From atomic_block.atomic_heap_lang Require Export lang proph_map.
From atomic_block.atomic_heap_lang Require Import tactics.
From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
Set Default Proof Using "Type".

Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_gen_heapG :> gen_heapG loc val Σ;
  heapG_proph_mapG :> proph_mapG proph_id val Σ
}.

Instance heapG_irisG `{heapG Σ} : irisG heap_lang Σ := {
  iris_invG := heapG_invG;
  state_interp σ κs _ :=
    (gen_heap_ctx σ.(heap) ∗ proph_map_ctx κs σ.(used_proph_id))%I;
  fork_post _ := True%I;
}.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l q v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (mapsto (L:=loc) (V:=val) l 1 v%V) (at level 20) : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Extern 0 (head_reducible_no_obs _ _) => eexists _, _, _; simpl : core.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Local Hint Extern 1 (head_step _ _ _ _ _ _) => econstructor : core.
Local Hint Extern 0 (head_step (CAS _ _ _) _ _ _ _ _) => eapply CasSucS : core.
Local Hint Extern 0 (head_step (CAS _ _ _) _ _ _ _ _) => eapply CasFailS : core.
Local Hint Extern 0 (head_step (Alloc _) _ _ _ _ _) => apply alloc_fresh : core.
Local Hint Extern 0 (head_step NewProph _ _ _ _ _) => apply new_proph_id_fresh : core.
Local Hint Resolve to_of_val : core.

Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
Instance as_val_val v : AsVal (Val v).
Proof. by eexists. Qed.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, atomic_ectx_language_atomic;
    [inversion 1; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver
    |done].

Instance alloc_atomic s v : Atomic s (Alloc (Val v)).
Proof. solve_atomic. Qed.
Instance load_atomic s v : Atomic s (Load (Val v)).
Proof. solve_atomic. Qed.
Instance store_atomic s v1 v2 : Atomic s (Store (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance cas_atomic s v0 v1 v2 : Atomic s (CAS (Val v0) (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance faa_atomic s v1 v2 : Atomic s (FAA (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Instance fork_atomic s e : Atomic s (Fork e).
Proof. solve_atomic. Qed.
Instance skip_atomic s  : Atomic s Skip.
Proof. solve_atomic. Qed.
Instance new_proph_atomic s : Atomic s NewProph.
Proof. solve_atomic. Qed.
Instance resolve_proph_atomic s v1 v2 : Atomic s (ResolveProph (Val v1) (Val v2)).
Proof. solve_atomic. Qed.

Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
Local Ltac solve_pure_exec :=
  subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Instance AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.

(* Pure reductions are automatically performed before any wp_ tactics
   handling impure operations. Since we do not want these tactics to
   unfold locked terms, we do not register this instance explicitely,
   but only activate it by hand in the `wp_rec` tactic, where we
   *actually* want it to unlock. *)
Lemma AsRecV_recv_locked v f x e :
  AsRecV v f x e → AsRecV (locked v) f x e.
Proof. by unlock. Qed.

Instance pure_recc f x (erec : expr) :
  PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
Proof. solve_pure_exec. Qed.
Instance pure_pairc (v1 v2 : val) :
  PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
Proof. solve_pure_exec. Qed.
Instance pure_injlc (v : val) :
  PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
Proof. solve_pure_exec. Qed.
Instance pure_injrc (v : val) :
  PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
Proof. solve_pure_exec. Qed.

Instance pure_beta f x (erec : expr) (v1 v2 : val) `{AsRecV v1 f x erec} :
  PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
Proof. unfold AsRecV in *. solve_pure_exec. Qed.

Instance pure_unop op v v' :
  PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
Proof. solve_pure_exec. Qed.

Instance pure_binop op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v').
Proof. solve_pure_exec. Qed.

Instance pure_if_true e1 e2 : PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
Proof. solve_pure_exec. Qed.

Instance pure_if_false e1 e2 : PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
Proof. solve_pure_exec. Qed.

Instance pure_fst v1 v2 :
  PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
Proof. solve_pure_exec. Qed.

Instance pure_snd v1 v2 :
  PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
Proof. solve_pure_exec. Qed.

Instance pure_case_inl v e1 e2 :
  PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
Proof. solve_pure_exec. Qed.

Instance pure_case_inr v e1 e2 :
  PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
Proof. solve_pure_exec. Qed.

Section lifting.
Context `{heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "He HΦ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 κ κs n) "Hσ !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. by iFrame.
Qed.

(** Heap *)
Lemma wp_alloc s E v :
  {{{ True }}} Alloc (Val v) @ s; E {{{ l, RET LitV (LitLoc l); l ↦ v }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>"; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_alloc with "Hσ") as "[Hσ Hl]"; first done.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.
Lemma abwp_alloc μs v :
  [[{ True }]] Alloc (Val v) @ μs [[{ l, RET LitV (LitLoc l); RET μs; l ↦ v }]].
Proof.
  iIntros (Φ) "_ HΦ". iApply abwp_lift_head_step; auto.
  iIntros (σ1 κs n) "[Hσ Hκs] !>"; iSplit; first by auto.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  rewrite app_nil_r.
  iMod (@gen_heap_alloc with "Hσ") as "[Hσ Hl]"; first done.
  iModIntro; iSplit=> //; iFrame.
  rewrite -abwp_value. by iApply "HΦ".
Qed.

Lemma wp_load s E l q v :
  {{{ ▷ l ↦{q} v }}} Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.
Lemma abwp_load μs l q v :
  [[{ l ↦{q} v }]] Load (Val $ LitV $ LitLoc l) @ μs [[{ RET v; RET μs; l ↦{q} v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply abwp_lift_head_step; auto.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  rewrite app_nil_r.
  iModIntro; iSplit=> //; iFrame.
  rewrite -abwp_value. by iApply "HΦ".
Qed.

Lemma wp_store s E l v' v :
  {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.
Lemma abwp_store μs l v' v :
  [[{ l ↦ v' }]] Store (Val $ LitV $ LitLoc l) (Val v) @ μs
  [[{ RET LitV LitUnit; RET μs; l ↦ v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply abwp_lift_head_step; auto.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  rewrite app_nil_r.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//; iFrame.
  rewrite -abwp_value. by iApply "HΦ".
Qed.

Lemma wp_cas_fail s E l q v' v1 v2 :
  v' ≠ v1 → vals_cas_compare_safe v' v1 →
  {{{ ▷ l ↦{q} v' }}} CAS (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET LitV (LitBool false); l ↦{q} v' }}}.
Proof.
  iIntros (?? Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.
Lemma abwp_cas_fail μs l q v' v1 v2 :
  v' ≠ v1 → vals_cas_compare_safe v' v1 →
  [[{ l ↦{q} v' }]] CAS (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ μs
  [[{ RET LitV (LitBool false); RET μs; l ↦{q} v' }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply abwp_lift_head_step; auto.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (κ v2' σ2 efs Hstep); inv_head_step.
  rewrite app_nil_r.
  iModIntro; iSplit=> //; iFrame.
  rewrite -abwp_value. by iApply "HΦ".
Qed.

Lemma wp_cas_suc s E l v1 v2 :
  vals_cas_compare_safe v1 v1 →
  {{{ ▷ l ↦ v1 }}} CAS (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET LitV (LitBool true); l ↦ v2 }}}.
Proof.
  iIntros (? Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.
Lemma abwp_cas_suc μs l v1 v2 :
  vals_cas_compare_safe v1 v1 →
  [[{ l ↦ v1 }]] CAS (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ μs
  [[{ RET LitV (LitBool true); RET μs; l ↦ v2 }]].
Proof.
  iIntros (? Φ) "Hl HΦ". iApply abwp_lift_head_step; auto.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (κ v2' σ2 efs Hstep); inv_head_step.
  rewrite app_nil_r.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//; iFrame.
  rewrite -abwp_value. by iApply "HΦ".
Qed.

Lemma wp_faa s E l i1 i2 :
  {{{ ▷ l ↦ LitV (LitInt i1) }}} FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E
  {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.
Lemma abwp_faa μs l i1 i2 :
  [[{ l ↦ LitV (LitInt i1) }]] FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ μs
  [[{ RET LitV (LitInt i1); RET μs; l ↦ LitV (LitInt (i1 + i2)) }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply abwp_lift_head_step; auto.
  iIntros (σ1 κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iIntros (κ e2 σ2 efs Hstep); inv_head_step.
  rewrite app_nil_r.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//; iFrame.
  rewrite -abwp_value. by iApply "HΦ".
Qed.

(** Lifting lemmas for creating and resolving prophecy variables *)
Lemma wp_new_proph :
  {{{ True }}} NewProph {{{ v (p : proph_id), RET (LitV (LitProphecy p)); proph p v }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ HR] !>". iDestruct "HR" as (R [Hfr Hdom]) "HR".
  iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep). inv_head_step.
  iMod (@proph_map_alloc with "HR") as "[HR Hp]".
  { intro Hin. apply (iffLR (elem_of_subseteq _ _) Hdom) in Hin. done. }
  iModIntro; iSplit=> //. iFrame. iSplitL "HR".
  - iExists _. iSplit; last done.
    iPureIntro. split.
    + apply first_resolve_insert; auto.
    + rewrite dom_insert_L. by apply union_mono_l.
  - iApply "HΦ". done.
Qed.

Lemma abwp_new_proph μs :
  [[{ True }]] NewProph @ μs [[{ v (p : proph_id), RET (LitV (LitProphecy p)); RET μs; proph p v }]].
Proof.
  iIntros (Φ) "_ HΦ". iApply abwp_lift_head_step; auto.
  iIntros (σ1 κs n) "[Hσ HR] !>". iDestruct "HR" as (R [Hfr Hdom]) "HR".
  iSplit; first by eauto.
  iIntros (κ v2 σ2 efs Hstep). inv_head_step.
  iMod (@proph_map_alloc with "HR") as "[HR Hp]".
  { intro Hin. apply (iffLR (elem_of_subseteq _ _) Hdom) in Hin. done. }
  iModIntro; iSplit=> //. iFrame. iSplitL "HR".
  - iExists _. iSplit; last done.
    iPureIntro. split.
    + apply first_resolve_insert; auto.
    + rewrite dom_insert_L. by apply union_mono_l.
  - rewrite app_nil_r -abwp_value. iApply "HΦ". done.
Qed.

Lemma wp_resolve_proph p v w:
  {{{ proph p v }}}
    ResolveProph (Val $ LitV $ LitProphecy p) (Val w)
  {{{ RET (LitV LitUnit); ⌜v = Some w⌝ }}}.
Proof.
  iIntros (Φ) "Hp HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n) "[Hσ HR] !>". iDestruct "HR" as (R [Hfr Hdom]) "HR".
  iDestruct (@proph_map_valid with "HR Hp") as %Hlookup.
  iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step. iApply fupd_frame_l.
  iSplit=> //. iFrame.
  iMod (@proph_map_remove with "HR Hp") as "Hp". iModIntro.
  iSplitR "HΦ".
  - iExists _. iFrame. iPureIntro. split; first by eapply first_resolve_delete.
    rewrite dom_delete. set_solver.
  - iApply "HΦ". iPureIntro. by eapply first_resolve_eq.
Qed.

Lemma abwp_resolve_proph μs p w:
  [[{ True }]]
    ResolveProph (Val $ LitV $ LitProphecy p) (Val w) @ μs
  [[{ RET (LitV LitUnit); RET μs ++ [(p, w)]; True }]].
Proof.
  iIntros (Φ) "_ HΦ". iApply abwp_lift_head_step; auto.
  iIntros (σ1 κs n) "[Hσ HR] !>".
  iSplit; first by eauto.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //; iFrame.
  rewrite -abwp_value. by iApply "HΦ".
Qed.

Lemma wp_atomic_block_fupd {s E Ψ Φ} (ab : expr) μs :
  ▷ ABWP ab @ [] [{v ; κ, Ψ v κ}] -∗
  ▷ (∀ v κ, Ψ v κ ={E}=∗ ⌜map fst μs = map fst κ⌝ ∗
                          ([∗ list] μ ∈ μs, proph (fst μ) (snd μ)) ∗
                          (⌜map snd μs = map (Some ∘ snd) κ⌝ -∗ Φ v)) -∗
  WP AtomicBlock ab @ s; E {{ Φ }}.
Proof.
  iIntros "HAB Hobs".
  iApply (wp_atomic_block_fupd with "HAB"); simpl in *; first done.
  iNext.
  iIntros (v κ κs σ _) "[Hh HPr] HΨ".
  iMod ("Hobs" with "HΨ") as "(Hfst & Hprs & HΦ)".
  iDestruct "Hfst" as %Hfst.
  iInduction (μs) as [|[p' w] μs] "IH" forall (κ κs σ Hfst); simpl in *.
  - destruct κ; last done; simpl in *. iFrame. iModIntro. by iApply "HΦ".
  - destruct κ as [|[p u] κ]; first done; simpl in *; simplify_eq.
    iDestruct "Hprs" as "[Hp Hprs]".
    iDestruct "HPr" as (R [Hfr Hdom]) "HPr".
    iDestruct (@proph_map_valid with "HPr Hp") as %Hlookup.
    iMod (@proph_map_remove with "HPr Hp") as "Hp".
    assert (w = Some u) as ->.
    { by eapply first_resolve_eq. }
    iApply ("IH" with "[] Hh [Hp] Hprs"); eauto.
    { iExists _. iFrame. iPureIntro. split; first by eapply first_resolve_delete.
    rewrite dom_delete. set_solver. }
    iIntros (?); iApply "HΦ".
    iPureIntro. by f_equal.
Qed.

End lifting.
