From iris.algebra Require Import auth excl.
From iris.heap_lang Require Import notation proofmode.
From iris.proofmode Require Import tactics.
From iris.heap_lang.lib Require Import par.
From iris_monotone Require Import monotone.
From stdpp Require Import relations.

Inductive ST : Set :=
| ST_zero_zero
| ST_zero_one
| ST_zero_one_then_one_one
| ST_one_zero
| ST_one_zero_then_one_one.

Global Instance ST_inhabited : Inhabited ST.
Proof. repeat constructor. Qed.

Definition ST_val (s : ST) : val * val :=
  match s with
  | ST_zero_zero => (#0, #0)
  | ST_zero_one => (#0, #1)
  | ST_zero_one_then_one_one => (#1, #1)
  | ST_one_zero => (#1, #0)
  | ST_one_zero_then_one_one => (#1, #1)
  end.

Canonical Structure STO := leibnizO ST.

Inductive ST_rel_base : STO → STO → Prop :=
| tr_zero_to_zero_one : ST_rel_base ST_zero_zero ST_zero_one
| tr_zero_to_one_zero : ST_rel_base ST_zero_zero ST_one_zero
| tr_zero_one_to_zero_one_then_one_one :
    ST_rel_base ST_zero_one ST_zero_one_then_one_one
| tr_one_zero_to_one_zero_then_one_one :
    ST_rel_base ST_one_zero ST_one_zero_then_one_one.

Definition ST_rel := rtc ST_rel_base.

Lemma ST_rel_succ_zero_one s :
  ST_rel ST_zero_one s → s = ST_zero_one ∨ s = ST_zero_one_then_one_one.
Proof.
  intros [?|[z [Hz1 Hz2]]]%rtc_inv; first by auto.
  inversion Hz1; subst.
  apply rtc_inv in Hz2 as [?|[w [Hw1 Hw2]]]; first by auto.
  inversion Hw1.
Qed.

Lemma ST_rel_succ_one_zero s :
  ST_rel ST_one_zero s → s = ST_one_zero ∨ s = ST_one_zero_then_one_one.
Proof.
  intros [?|[z [Hz1 Hz2]]]%rtc_inv; first by auto.
  inversion Hz1; subst.
  apply rtc_inv in Hz2 as [?|[w [Hw1 Hw2]]]; first by auto.
  inversion Hw1.
Qed.

Lemma ST_rel_succ_zero_one_then_one_one s :
  ST_rel ST_zero_one_then_one_one s → s = ST_zero_one_then_one_one.
Proof.
  intros [?|[z [Hz1 Hz2]]]%rtc_inv; first by auto.
  inversion Hz1; subst.
Qed.

Lemma ST_rel_succ_one_zero_then_one_one s :
  ST_rel ST_one_zero_then_one_one s → s = ST_one_zero_then_one_one.
Proof.
  intros [?|[z [Hz1 Hz2]]]%rtc_inv; first by auto.
  inversion Hz1; subst.
Qed.

Definition prog : expr :=
  let: "x" := ref #0 in
  let: "y" := ref #0 in
  ("x" <- #1;; !"y") ||| ("y" <- #1;; !"x").

Section verification.
  Context `{!heapG Σ, spawnG Σ, !inG Σ (authUR (monotoneUR ST_rel)),
            !inG Σ (exclR unitR)}.

  Definition observed_ST (γ : gname) (s : ST) : iProp Σ :=
    own γ (◯ (principal ST_rel s)).

  Global Instance observed_ST_persistent γ s : Persistent (observed_ST γ s).
  Proof. apply _. Qed.

  Definition exact_ST (γ : gname) (s : ST) : iProp Σ :=
    own γ (● (principal ST_rel s)).

  Lemma alloc_exact_zero_zero : ⊢ |==> ∃ γ, exact_ST γ ST_zero_zero.
  Proof. by iApply own_alloc; apply auth_auth_valid. Qed.

  Lemma observe γ s : exact_ST γ s ==∗ exact_ST γ s ∗ observed_ST γ s.
  Proof.
    iIntros "H".
    iMod (own_update _ _ ((● (principal ST_rel s)) ⋅ (◯ (principal ST_rel s)))
            with "H") as "[$ $]"; last done.
    apply auth_update_alloc.
    apply local_update_unital_discrete.
    intros ? ?; rewrite left_id; intros <-.
    split; first done.
    by rewrite principal_R_op; last constructor.
  Qed.

  Lemma observed_rel γ s s' : exact_ST γ s' -∗ observed_ST γ s -∗ ⌜ST_rel s s'⌝.
  Proof.
    iIntros "H1 H2".
    by iDestruct (own_valid_2 with "H1 H2") as
        %[?%(principal_included (R := ST_rel)) _]%auth_both_valid.
  Qed.

  Lemma update_ST γ s s' :
    ST_rel s s' → exact_ST γ s ==∗ exact_ST γ s' ∗ observed_ST γ s'.
  Proof.
    iIntros (Hs) "H".
    iMod (own_update _ _ ((● (principal ST_rel s')) ⋅ (◯ (principal ST_rel s')))
            with "H") as "[$ $]"; last done.
    apply auth_update_alloc.
    apply local_update_unital_discrete.
    intros ? ?; rewrite left_id; intros <-.
    split; first done.
    by rewrite (comm op) (principal_R_op s s').
  Qed.

  Definition inv_name : namespace := nroot.@"inv".

  Definition prog_inv γ lx ly : iProp Σ :=
    ∃ s, exact_ST γ s ∗ lx ↦{1/2} (ST_val s).1 ∗ ly ↦{1/2} (ST_val s).2.

  Lemma prog_inv_update_lx_to_one γ lx ly :
    prog_inv γ lx ly -∗ lx ↦{1/2} #0 -∗
      lx ↦ #0 ∗ (lx ↦{1/2} #1 ==∗
      prog_inv γ lx ly ∗
      (observed_ST γ ST_one_zero ∨
       observed_ST γ ST_zero_one_then_one_one)).
  Proof.
    iDestruct 1 as (s) "(Hs & Hlx & Hly)".
    iIntros "Hlx'".
    iDestruct (mapsto_agree with "Hlx Hlx'") as %Heq.
    rewrite Heq.
    iCombine "Hlx" "Hlx'" as "Hlx".
    iFrame.
    iIntros "Hlx".
    destruct s; simpl in *; [| |done|done|done].
    - iMod (update_ST _ _ ST_one_zero with "Hs") as "[Hs Hob]";
        first by eapply rtc_once; constructor.
      iModIntro.
      iDestruct "Hlx" as "[Hlx Hlx']".
      iSplitR "Hob"; last by iFrame.
      iExists _; iFrame.
    - iMod (update_ST _ _ ST_zero_one_then_one_one with "Hs") as "[Hs Hob]";
        first by eapply rtc_once; constructor.
      iModIntro.
      iDestruct "Hlx" as "[Hlx Hlx']".
      iSplitR "Hob"; last by iFrame.
      iExists _; iFrame.
  Qed.

  Lemma prog_inv_update_ly_to_one γ lx ly :
    prog_inv γ lx ly -∗ ly ↦{1/2} #0 -∗
      ly ↦ #0 ∗ (ly ↦{1/2} #1 ==∗
      prog_inv γ lx ly ∗
      (observed_ST γ ST_zero_one ∨
       observed_ST γ ST_one_zero_then_one_one)).
  Proof.
    iDestruct 1 as (s) "(Hs & Hlx & Hly)".
    iIntros "Hly'".
    iDestruct (mapsto_agree with "Hly Hly'") as %Heq.
    rewrite Heq.
    iCombine "Hly" "Hly'" as "Hly".
    iFrame.
    iIntros "Hly".
    destruct s; simpl in *; [|done|done| |done].
    - iMod (update_ST _ _ ST_zero_one with "Hs") as "[Hs Hob]";
        first by eapply rtc_once; constructor.
      iModIntro.
      iDestruct "Hlx" as "[Hlx Hlx']".
      iSplitR "Hob"; last by iFrame.
      iExists _; iFrame.
    - iMod (update_ST _ _ ST_one_zero_then_one_one with "Hs") as "[Hs Hob]";
        first by eapply rtc_once; constructor.
      iModIntro.
      iDestruct "Hlx" as "[Hlx Hlx']".
      iSplitR "Hob"; last by iFrame.
      iExists _; iFrame.
  Qed.

  Definition left_post (γ : gname) (v: val) : iProp Σ :=
    (⌜v = #0⌝ ∗ (observed_ST γ ST_one_zero)) ∨
     (⌜v = #1⌝ ∗ ((observed_ST γ ST_zero_one_then_one_one) ∨
                  (observed_ST γ ST_one_zero_then_one_one))).

  Definition right_post (γ : gname) (v: val) : iProp Σ :=
    (⌜v = #0⌝ ∗ (observed_ST γ ST_zero_one)) ∨
     (⌜v = #1⌝ ∗ ((observed_ST γ ST_zero_one_then_one_one) ∨
                  (observed_ST γ ST_one_zero_then_one_one))).

  Lemma prog_inv_read_lx γ lx ly :
    prog_inv γ lx ly -∗
      observed_ST γ ST_zero_one ∨ observed_ST γ ST_one_zero_then_one_one -∗
      ∃ s, lx ↦{1/2} (ST_val s).1 ∗ (lx ↦{1/2} (ST_val s).1 ==∗
             prog_inv γ lx ly ∗ right_post γ (ST_val s).1).
  Proof.
    unfold right_post.
    iDestruct 1 as (s) "(Hs & Hlx & Hly)".
    iIntros "#Hobs".
    iExists _; iFrame "Hlx".
    iIntros "Hlx".
    destruct s; simpl.
    - iDestruct "Hobs" as "[Hobs|Hobs]".
      + by iDestruct (observed_rel with "Hs Hobs") as %[|]%ST_rel_succ_zero_one.
      + by iDestruct (observed_rel with "Hs Hobs")
            as %?%ST_rel_succ_one_zero_then_one_one.
    - iMod (observe with "Hs") as "[Hs #Hobs']".
      iModIntro.
      iSplitL; last by eauto.
      iExists _; iFrame; simpl; iFrame.
    - iMod (observe with "Hs") as "[Hs #Hobs']".
      iSplitL; last by eauto.
      iModIntro.
      iExists _; iFrame; simpl; iFrame.
    - iDestruct "Hobs" as "[Hobs|Hobs]".
      + by iDestruct (observed_rel with "Hs Hobs") as %[|]%ST_rel_succ_zero_one.
      + by iDestruct (observed_rel with "Hs Hobs")
            as %?%ST_rel_succ_one_zero_then_one_one.
    - iMod (observe with "Hs") as "[Hs #Hobs']".
      iModIntro.
      iSplitL; last by eauto.
      iExists _; iFrame; simpl; iFrame.
  Qed.

  Lemma prog_inv_read_ly γ lx ly :
    prog_inv γ lx ly -∗
      observed_ST γ ST_one_zero ∨ observed_ST γ ST_zero_one_then_one_one -∗
      ∃ s, ly ↦{1/2} (ST_val s).2 ∗ (ly ↦{1/2} (ST_val s).2 ==∗
             prog_inv γ lx ly ∗ left_post γ (ST_val s).2).
  Proof.
    unfold left_post.
    iDestruct 1 as (s) "(Hs & Hlx & Hly)".
    iIntros "#Hobs".
    iExists _; iFrame "Hly".
    iIntros "Hly".
    destruct s; simpl.
    - iDestruct "Hobs" as "[Hobs|Hobs]".
      + by iDestruct (observed_rel with "Hs Hobs") as %[|]%ST_rel_succ_one_zero.
      + by iDestruct (observed_rel with "Hs Hobs")
            as %?%ST_rel_succ_zero_one_then_one_one.
    - iDestruct "Hobs" as "[Hobs|Hobs]".
      + by iDestruct (observed_rel with "Hs Hobs") as %[|]%ST_rel_succ_one_zero.
      + by iDestruct (observed_rel with "Hs Hobs")
            as %?%ST_rel_succ_zero_one_then_one_one.
    - iMod (observe with "Hs") as "[Hs #Hobs']".
      iModIntro.
      iSplitL; last by eauto.
      iExists _; iFrame; simpl; iFrame.
    - iMod (observe with "Hs") as "[Hs #Hobs']".
      iSplitL; last by eauto.
      iModIntro.
      iExists _; iFrame; simpl; iFrame.
    - iMod (observe with "Hs") as "[Hs #Hobs']".
      iModIntro.
      iSplitL; last by eauto.
      iExists _; iFrame; simpl; iFrame.
  Qed.

  Lemma prog_wp :
    ⊢ WP prog {{v, ⌜v = (#0, #1)%V⌝ ∨ ⌜v = (#1, #0)%V⌝ ∨ ⌜v = (#1, #1)%V⌝}}.
  Proof.
    unfold prog.
    wp_alloc lx as "[Hlx Hlx']".
    wp_let.
    wp_alloc ly as "[Hly Hly']".
    wp_let.
    iMod alloc_exact_zero_zero as (γ) "Hex".
    iMod (inv_alloc inv_name _ (prog_inv γ lx ly) with "[Hlx' Hly' Hex]")
      as "#Hinv".
    { iNext; iExists _; iFrame. }
    wp_pures.
    iApply wp_fupd.
    iApply (par_spec (left_post γ) (right_post γ)
              with "[Hlx] [Hly] []"); simpl.
    - wp_lam.
      wp_bind (_ <- _)%E.
      iInv inv_name as ">Hri" "Hcl".
      iDestruct (prog_inv_update_lx_to_one with "Hri Hlx") as "[Hlx Hupd]".
      wp_store.
      iDestruct "Hlx" as "[Hlx Hlx']".
      iMod ("Hupd" with "Hlx'") as "[Hri #Hobs]".
      iMod ("Hcl" with "Hri") as "_".
      iModIntro.
      wp_pures.
      iInv inv_name as "Hri" "Hcl".
      iDestruct (prog_inv_read_ly with "Hri []")
        as (s') "[Hl Hupd]"; first done.
      wp_load.
      iMod ("Hupd" with "Hl") as "[Hri Hp]".
      iMod ("Hcl" with "Hri") as "_".
      done.
    - wp_lam.
      wp_bind (_ <- _)%E.
      iInv inv_name as ">Hri" "Hcl".
      iDestruct (prog_inv_update_ly_to_one with "Hri Hly") as "[Hly Hupd]".
      wp_store.
      iDestruct "Hly" as "[Hly Hly']".
      iMod ("Hupd" with "Hly'") as "[Hri #Hobs]".
      iMod ("Hcl" with "Hri") as "_".
      iModIntro.
      wp_pures.
      iInv inv_name as ">Hri" "Hcl".
      iDestruct (prog_inv_read_lx with "Hri []")
        as (s') "[Hl Hupd]"; first done.
      wp_load.
      iMod ("Hupd" with "Hl") as "[Hri Hp]".
      iMod ("Hcl" with "Hri") as "_".
      done.
    - iNext.
      iIntros (v1 v2).
      unfold left_post, right_post.
      iIntros "[[[% Hleft]|[% Hleft]] [[% Hright]|[% Hright]]]"; subst; eauto.
      iNext.
      iInv inv_name as (s) "(>Hs & Hlx & Hly)" "Hcl".
      iDestruct (observed_rel with "Hs Hleft") as %[|]%ST_rel_succ_one_zero;
        iDestruct (observed_rel with "Hs Hright") as %[|]%ST_rel_succ_zero_one;
        simplify_eq.
  Qed.

End verification.
