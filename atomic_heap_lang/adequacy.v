From iris.program_logic Require Export weakestpre adequacy.
From iris.algebra Require Import auth.
From atomic_block.atomic_heap_lang Require Import proofmode notation proph_map.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Class heapPreG Σ := HeapPreG {
  heap_preG_iris :> invPreG Σ;
  heap_preG_heap :> gen_heapPreG loc val Σ;
  heap_preG_proph :> proph_mapPreG proph_id val Σ
}.

Definition heapΣ : gFunctors := #[invΣ; gen_heapΣ loc val; proph_mapΣ proph_id val].
Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapPreG Σ.
Proof. solve_inG. Qed.

Definition heap_adequacy Σ `{heapPreG Σ} s e σ φ :
  (∀ `{heapG Σ}, WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}%I) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (??) "".
  iMod (gen_heap_init σ.(heap)) as (?) "Hh".
  iMod (proph_map_init κs σ.(used_proph_id)) as (?) "Hp".
  iModIntro.
  iExists (λ σ κs, (gen_heap_ctx σ.(heap) ∗ proph_map_ctx κs σ.(used_proph_id))%I). iFrame.
  iApply (Hwp (HeapG _ _ _ _)).
Qed.
