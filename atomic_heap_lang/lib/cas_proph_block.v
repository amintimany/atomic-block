From atomic_block.atomic_heap_lang Require Import lang.
From iris.proofmode Require Import tactics.
From atomic_block.atomic_heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

Definition resolve_list: val :=
  rec: "f" "x" :=
    match: ! "x" with
      NONE => #()
    | SOME "p" =>
      ResolveProph (Fst (Fst "p")) (Snd (Fst "p"));; "f" (Snd "p")
    end.

Definition cas_resolve_list: val :=
  λ: "v1" "v2" "v3" "κs",
  AtomicBlock
    (if: CAS "v1" "v2" "v3" then resolve_list "κs" ;; #true else #false).

Section resolve_list.
  Context `{!heapG Σ}.

  Fixpoint obs_list (l : list observation) (v : val) : iProp Σ :=
    match l with
    | [] => ∃ (l : loc), ⌜v = # l⌝ ∗ l ↦ NONEV
    | pv :: l' =>
      ∃ (l : loc) w, ⌜v = # l⌝
        ∗ l ↦ SOMEV (PairV (PairV (#(fst pv)) (snd pv)) w)
        ∗ obs_list l' w
    end%I.

  Lemma abwp_resolve_list μs κs v :
    [[{ obs_list κs v }]]
      resolve_list v @ μs
    [[{ RET #(); RET μs ++ κs; obs_list κs v}]].
  Proof.
    iIntros (Φ) "Hob HΦ".
    iInduction (κs) as [|[p w] κs] "IH" forall (μs v); simpl.
    - rewrite /resolve_list.
      iDestruct "Hob" as (l ->) "Hl".
      wp_rec. wp_load. wp_case. wp_seq.
      rewrite app_nil_r.
      by iApply "HΦ"; iExists _; iFrame.
    -  rewrite /resolve_list.
      iDestruct "Hob" as (l u) "(-> & Hl & Hob)".
      wp_rec. wp_load. wp_case. wp_let.
      repeat wp_proj.
      wp_apply (abwp_resolve_proph); first done.
      iIntros "_". wp_seq.
      repeat wp_proj.
      iApply ("IH" with "Hob").
      rewrite -app_assoc /=.
      iIntros "Hob".
      by iApply "HΦ"; iExists _, _; iFrame.
  Qed.

  Lemma abwp_cas_resolve_list_suc E1 l v1 (v3 : val) κs w prs :
    vals_cas_compare_safe v1 v1 →
    map fst prs = map fst κs →
    {{{ ▷ (obs_list κs w ∗ l ↦ v1 ∗ [∗ list] μ ∈ prs, proph μ.1 μ.2) }}}
      cas_resolve_list #l v1 v3 w @ E1
    {{{ RET #true; obs_list κs w ∗ l ↦ v3 ∗ ⌜map snd prs = map (Some ∘ snd) κs⌝}}}.
  Proof.
    iIntros (Hvls Hprsκs Φ) "(Hob & Hl & Hprs) HΦ".
    rewrite /cas_resolve_list.
    wp_lam. repeat wp_let. (* weird behavior! *)
    iApply (wp_atomic_block_fupd
              (Ψ := λ v κs', (obs_list κs w ∗ ⌜κs = κs'⌝ ∗
                              l ↦ v3 ∗ ⌜v = #true⌝)) with "[Hl Hob]")%I.
    - iNext.
      wp_apply (abwp_cas_suc with "Hl"); first done.
      iIntros "Hl".
      wp_if.
      wp_apply (abwp_resolve_list with "Hob"); simpl.
      iIntros "Hob".
      wp_seq. by iFrame.
    - iNext. iIntros (v κ) "HΨ".
      iDestruct "HΨ" as "(Hκs & -> & Hl & ->)".
      iModIntro; iFrame.
      iSplit; first done.
      iIntros "Hsnd".
      by iApply "HΦ"; iFrame.
  Qed.

  Lemma abwp_cas_resolve_list_fail E1 l v1 v2 (v3 w : val) :
    vals_cas_compare_safe v1 v2 →
    v1 ≠ v2 →
    {{{ ▷ l ↦ v1 }}} cas_resolve_list #l v2 v3 w @ E1 {{{ RET #false; l ↦ v1 }}}.
  Proof.
    iIntros (Hvls Hprsκs Φ) "Hl HΦ".
    rewrite /cas_resolve_list.
    wp_lam. repeat wp_let. (* weird behavior! *)
    iApply (wp_atomic_block_fupd _ []
              (Ψ := λ v κs, l ↦ v1 ∗ ⌜κs = []⌝ ∗ ⌜v = #false⌝) with "[Hl]")%I.
    - iNext.
      wp_apply (abwp_cas_fail with "Hl"); auto.
      iIntros "Hl".
      by wp_if; iFrame.
    - iNext. iIntros (v κ) "HΨ".
      iDestruct "HΨ" as "(Hl & -> & ->)".
      iModIntro; iFrame.
      iSplit; first done.
      rewrite big_opL_nil left_id.
      iIntros "_".
      by iApply "HΦ"; iFrame.
  Qed.

End resolve_list.
