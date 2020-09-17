From iris.algebra Require Import auth frac gmap agree.
From iris.base_logic Require Import invariants.
From iris.heap_lang Require Import proofmode notation tactics.
From iris.program_logic Require Import weakestpre.
From iris_monotone Require Import monotone.


(** An example of using the monotone monoid construction to create
    monotone refrences. *)

Section Resources.
  Context {A : ofeT} {R : relation A}.

  Class MonRefG Σ := monrefG {
    MonRefIG_monauth :> inG Σ (authUR (monotoneUR R));
  }.

  Definition MonRefΣ :=
    #[GFunctor (authUR (monotoneUR R))].

  Instance subG_MonRefIGΣ {Σ} : subG MonRefΣ Σ → MonRefG Σ.
  Proof. solve_inG. Qed.
End Resources.

Global Arguments MonRefG {_} _ _.

Section MonRef.
  Context {A : ofeT} (R : relation A) `{!ProperPreOrder R}.
  Context (to_A : val heap_lang → option A).
  Context `{!MonRefG R Σ, !heapG Σ}.

  Definition Exact γ v :=
    (∃ a, ⌜to_A v = Some a⌝ ∗ own γ (● (principal R a)))%I.

  Definition atleast_def γ v :=
    (∃ a, ⌜to_A v = Some a⌝ ∗ own γ (◯ (principal R a)))%I.
  Definition atleast_aux γ v : seal (atleast_def γ v). by eexists. Qed.
  Definition atleast γ v : iProp Σ := (atleast_aux γ v).(unseal).
  Definition atleast_eq γ v : atleast γ v = atleast_def γ v :=
    (atleast_aux γ v).(seal_eq).

  Lemma MonRef_related γ v w :
    Exact γ v -∗ atleast γ w -∗
               ∃ a b, ⌜to_A w = Some a ∧ to_A v = Some b ∧ R a b⌝.
  Proof.
    rewrite atleast_eq /atleast_def.
    iIntros "HF Hf".
    iDestruct "HF" as (a ->) "HF".
    iDestruct "Hf" as (b ->) "Hf".
    iDestruct (own_valid_2 with "HF Hf") as %[Hvl _]%auth_both_valid;
      simpl in *.
    iPureIntro; simpl.
    apply (principal_included b a) in Hvl; eauto.
  Qed.

  Global Instance atleas_presistent l v : Persistent (atleast l v).
  Proof. rewrite atleast_eq /atleast_def; apply _. Qed.

  Definition MonRefMapsto_def l γ v :=
    (Exact γ v ∗ l ↦ v)%I.
  Definition MonRefMapsto_aux l γ v : seal (MonRefMapsto_def l γ v).
  Proof. by eexists. Qed.
  Definition MonRefMapsto l γ v : iProp Σ := (MonRefMapsto_aux l γ v).(unseal).
  Definition MonRefMapsto_eq l γ v :
    MonRefMapsto l γ v = MonRefMapsto_def l γ v :=
    (MonRefMapsto_aux l γ v).(seal_eq).

  Lemma MonRef_alloc v a :
    to_A v = Some a → ⊢ (|==> ∃ γ, Exact γ v ∗ atleast γ v)%I.
  Proof.
    setoid_rewrite atleast_eq. rewrite /atleast_def /Exact.
    iIntros (Hv).
    iMod (own_alloc (● (principal R a) ⋅ ◯ (principal R a))) as (γ) "[HF Hf]".
    { by apply auth_both_valid. }
    iModIntro; iExists _; iSplitL "HF"; iFrame; eauto.
  Qed.

  Lemma MonRef_update γ v w a b :
    to_A v = Some a → to_A w = Some b → R a b →
    Exact γ v ==∗ Exact γ w ∗ atleast γ w.
  Proof.
    rewrite atleast_eq /atleast_def.
    iIntros (Hv Hw HR) "HF".
    iDestruct "HF" as (c Hc) "HF"; simplify_eq.
    iMod (own_update _ _ (● (principal R b) ⋅ ◯ (principal R b))
            with "HF") as "[HF Hf]".
    { apply auth_update_alloc.
      by apply monotone_local_update_grow. }
    iModIntro; iSplitL "HF"; iExists _; iSplit; eauto.
  Qed.

  Lemma MonRefAlloc l v a :
    to_A v = Some a → l ↦ v ==∗ ∃ γ, MonRefMapsto l γ v.
  Proof.
    iIntros (Hv) "Hl".
    iMod (MonRef_alloc v a) as (γ) "[HE Hal]"; eauto.
    iModIntro. iExists _.
    rewrite MonRefMapsto_eq /MonRefMapsto_def. iFrame.
  Qed.

  Lemma MonRefDealloc l γ v :
    MonRefMapsto l γ v -∗
     ∃ a, ⌜to_A v = Some a⌝ ∗ l ↦ v ∗
       ∃ P, P ∗ (P -∗ ∀ w b, ⌜to_A w = Some b ∧ R a b⌝ -∗
                       l ↦ w ==∗ MonRefMapsto l γ w).
  Proof.
    rewrite MonRefMapsto_eq /MonRefMapsto_def.
    iIntros "(HE & Hl)".
    iDestruct "HE" as (a) "[% HE]".
    iExists _; iSplit; first by eauto.
    iFrame.
    iExists (Exact γ v)%I; iFrame.
    iSplitL.
    { iExists _; iFrame; eauto. }
    iIntros "HE". iIntros (w c [Hc Hac]) "Hl".
    iMod (MonRef_update _ _ w with "HE") as "[HE HA]"; eauto.
    rewrite MonRefMapsto_eq /MonRefMapsto_def; iFrame; auto.
  Qed.

  Lemma wp_Create_MonRef E (v : val heap_lang) :
    {{{ ∃ a, ⌜to_A v = Some a⌝ }}}
      Alloc v @ E
    {{{l γ, RET #l; MonRefMapsto l γ v }}}.
  Proof.
    iIntros (F) "H HF". iDestruct "H" as (a) "%".
    iApply wp_fupd.
    wp_alloc l as "Hl".
    iMod (MonRefAlloc with "Hl") as (γ) "H"; eauto.
    by iModIntro; iApply "HF".
  Qed.

  Lemma wp_Read_MonRef E l γ (v : val heap_lang) :
    {{{ MonRefMapsto l γ v }}}
      ! #l @ E
    {{{RET v; MonRefMapsto l γ v }}}.
  Proof.
    rewrite MonRefMapsto_eq /MonRefMapsto_def.
    iIntros (F) "H HF".
    iDestruct "H" as "(HE & Hal & Hl)".
    wp_load.
    iApply "HF"; iFrame "#"; iFrame.
  Qed.

  Lemma wp_Write_MonRef E l γ (v w : val heap_lang) a b :
    to_A v = Some a → to_A w = Some b → R a b →
    {{{ MonRefMapsto l γ v }}}
      #l <- w @ E
    {{{RET #(); MonRefMapsto l γ w }}}.
  Proof.
    rewrite MonRefMapsto_eq /MonRefMapsto_def.
    iIntros (Hv Hw HR Φ) "H HΦ".
    iDestruct "H" as "[HE Hl]".
    iApply wp_fupd.
    wp_store.
    iMod (MonRef_update with "HE") as "[HE HFr']"; eauto.
    iModIntro. iApply "HΦ".
    rewrite MonRefMapsto_eq /MonRefMapsto_def; iFrame.
  Qed.

  Lemma snap_shot l γ v : MonRefMapsto l γ v ==∗ MonRefMapsto l γ v ∗ atleast γ v.
  Proof.
    rewrite MonRefMapsto_eq /MonRefMapsto_def.
    iIntros "[HE Hl]"; eauto.
    iDestruct "HE" as (a) "[% HE]".
    iMod (MonRef_update _ v v with "[HE]") as "[HE HFr']";
      [eauto|eauto|reflexivity| |by iFrame].
    iExists _; iFrame; done.
  Qed.

  Lemma recall l γ v w :
    atleast γ w -∗ MonRefMapsto l γ v -∗
            ∃ a b, ⌜to_A w = Some a ∧ to_A v = Some b ∧ R a b⌝.
  Proof.
    rewrite MonRefMapsto_eq /MonRefMapsto_def.
    iIntros "Hal (HE & Hal' & Hl)".
    iDestruct (MonRef_related with "HE Hal") as "?"; eauto.
  Qed.

End MonRef.
