From iris.algebra Require Import auth numbers.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import weakestpre.
From iris.heap_lang Require Import proofmode notation tactics.

Definition mk_counter : val := λ: <>, ref #0.
Definition counter_incr : val :=
  rec: "f" "c" :=
    let: "r" := !"c" in
    if: CAS "c" "r" ("r" + #1) then #() else "f" "c".
Definition counter_read : val := λ: "c", !"c".

Section mono_counter.
  Context `{!heapG Σ, inG Σ (authUR max_natUR)}.

  Definition counter_exact (γ : gname) (n : nat) := own γ (● (MaxNat n)).

  Definition counter_atleast (γ : gname) (n : nat) := own γ (◯ (MaxNat n)).

  Lemma counter_exact_at_least γ n m :
    counter_exact γ n -∗ counter_atleast γ m -∗ ⌜m ≤ n⌝.
  Proof.
    iIntros "HF Hf".
    iDestruct (own_valid_2 with "HF Hf") as
        %[Hvl%max_nat_included _]%auth_both_valid; done.
  Qed.

  Definition inv_name := nroot .@ "inv".

  Definition is_counter (c : loc) (γ : gname) :=
    inv inv_name (∃ n : nat, c ↦ #n ∗ counter_exact γ n).

  Lemma wp_mk_counter :
    {{{ True }}}
      mk_counter #()
    {{{(c : loc) γ, RET #c; is_counter c γ ∗ counter_atleast γ 0 }}}.
  Proof.
    unfold mk_counter.
    iIntros (Φ) "_ HΦ".
    wp_pures.
    iApply wp_fupd.
    wp_alloc c as "Hc".
    iMod (own_alloc (● (MaxNat 0) ⋅ ◯ (MaxNat 0))) as (γ) "[Hfl Hfr]".
    { apply auth_both_valid; split; last done.
      apply max_nat_included; done. }
    iMod (inv_alloc inv_name _ (∃ n : nat, c ↦ #n ∗ counter_exact γ n)
            with "[Hc Hfl]").
    { iNext; iExists _; iFrame. }
    iModIntro.
    iApply "HΦ"; iFrame; done.
  Qed.

  Lemma wp_counter_incr c γ :
    {{{ is_counter c γ }}} counter_incr #c {{{RET #(); True}}}.
  Proof.
    iIntros (Φ) "#Hinv HΦ".
    unfold counter_incr.
    iLöb as "IH".
    wp_pures.
    wp_bind (! _)%E.
    iInv inv_name as (n) "[Hc Hfl]".
    wp_load.
    iModIntro.
    iSplitL "Hc Hfl".
    { iNext; iExists _; iFrame. }
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    iInv inv_name as (m) "[Hc Hfl]".
    destruct (decide (n = m)) as [->|].
    - wp_cmpxchg_suc.
      iMod (own_update with "Hfl") as "[Hfl _]".
      { apply auth_update_alloc.
        apply (max_nat_local_update _ _ (MaxNat (m + 1))); simpl; lia. }
      replace (m + 1)%Z with (m + 1 : Z) by lia.
      iModIntro.
      iSplitL "Hc Hfl".
      { iNext; iExists _; iFrame. }
      wp_pures.
      iApply "HΦ"; done.
    - wp_cmpxchg_fail; first naive_solver.
      iModIntro.
      iSplitL "Hc Hfl".
      { iNext; iExists _; iFrame. }
      do 2 wp_pure _.
      iApply "IH"; done.
  Qed.

  Lemma wp_counter_read c γ n :
    {{{ is_counter c γ ∗ counter_atleast γ n }}}
      counter_read #c
    {{{(m : nat), RET #m; ⌜n ≤ m⌝ ∗ counter_atleast γ m}}}.
  Proof.
    iIntros (Φ) "#[Hinv Hn] HΦ".
    unfold counter_read.
    wp_pures.
    iInv inv_name as (m) "[Hc Hfl]".
    wp_load.
    iDestruct (counter_exact_at_least with  "Hfl Hn") as %?.
    iMod (own_update with "Hfl") as "[Hfl Hm]".
    { apply auth_update_alloc.
      apply (max_nat_local_update _ _ (MaxNat m)); simpl; lia. }
    iModIntro.
    iSplitL "Hc Hfl".
    { iNext; iExists _; iFrame. }
    iApply "HΦ"; iFrame; done.
  Qed.

End mono_counter.
