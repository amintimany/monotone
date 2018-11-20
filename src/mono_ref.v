From iris.algebra Require Import auth frac gmap agree.
From iris.base_logic Require Import invariants.
From iris.heap_lang Require Import proofmode notation tactics.
From iris.program_logic Require Import weakestpre.
From iris_monotone Require Import monotone.


(** An example of using the monotone monoid construction to create
    monotone refrences. *)

Section Resources.
  Context {A : ofeT} {R : relation A} `{!ProperPreOrder R}.

  Class MonRefG Σ := monrefG {
    MonRefIG_monauth :> inG Σ (authUR (optionUR (monotoneR R)));
    MonRefIG_register :> inG Σ (authUR (gmapUR loc (agreeR (leibnizC gname))));
    MonRefIG_register_name : gname;
  }.

  Class MonRefPreG Σ := monrefPreG {
    MonRefPreIG_monauth :> inG Σ (authUR (optionUR (monotoneR R)));
    MonRefPreIG_register :> inG Σ (authUR (gmapUR loc (agreeR (leibnizC gname))));
  }.

  Definition MonRefΣ :=
    #[GFunctor (authUR (optionUR (monotoneR R)));
        GFunctor (authUR (gmapUR loc (agreeR (leibnizC gname))))].

  Instance subG_MonRefIGΣ {Σ} : subG MonRefΣ Σ → MonRefPreG Σ.
  Proof. solve_inG. Qed.
End Resources.

Global Arguments MonRefG {_} _ {_} _.

Section MonRef.
  Context {A : ofeT} (R : relation A) `{!ProperPreOrder R}.
  Context (to_A : val → option A).
  Context `{!MonRefG R Σ, !heapG Σ}.

  Definition MonRefN := nroot .@ "MonoRef".

  Definition toRegister (M : gmap loc gname) :
    gmapUR loc (agreeR (leibnizC gname)) := (λ x, to_agree x) <$> M.

  Definition LocRegister M := own MonRefIG_register_name (● toRegister M).
  Definition registered l (γ : gname) :=
    own MonRefIG_register_name (◯ {[l := to_agree γ]}).

  Lemma registered_agree l γ γ' : registered l γ -∗ registered l γ' -∗ ⌜γ = γ'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvl.
    iPureIntro.
    specialize (Hvl l); revert Hvl;
      rewrite /= lookup_op !lookup_singleton -Some_op Some_valid.
      intros Hvl%@agree_op_inv'; eauto.
  Qed.

  Definition MonRefFull γ v :=
    (∃ a, ⌜to_A v = Some a⌝ ∗ own γ (● (Some (principal R a))))%I.

  Definition MonRefFrag γ v :=
    (∃ a, ⌜to_A v = Some a⌝ ∗ own γ (◯ (Some (principal R a))))%I.

  Lemma MonRef_related γ v w :
    MonRefFull γ v -∗ MonRefFrag γ w -∗
               ∃ a b, ⌜to_A w = Some a ∧ to_A v = Some b ∧ R a b⌝.
  Proof.
    iIntros "HF Hf".
    iDestruct "HF" as (a ->) "HF".
    iDestruct "Hf" as (b ->) "Hf".
    iDestruct (own_valid_2 with "HF Hf") as %[Hvl _]%auth_valid_discrete;
      simpl in *.
    iPureIntro; simpl.
    revert Hvl; rewrite left_id; intros [Hvl|Hvl]%Some_included.
    - specialize (Hvl O). apply principal_injN_general in Hvl.
      destruct Hvl; eauto.
    - apply principal_included in Hvl. eauto.
  Qed.

  Definition atleast_def l v := (∃ γ, registered l γ ∗ MonRefFrag γ v)%I.
  Definition atleast_aux l v : seal (atleast_def l v). by eexists. Qed.
  Definition atleast l v : iProp Σ := (atleast_aux l v).(unseal).
  Definition atleast_eq l v : atleast l v = atleast_def l v :=
    (atleast_aux l v).(seal_eq).

  Global Instance atleas_presistent l v : Persistent (atleast l v).
  Proof. rewrite atleast_eq /atleast_def; apply _. Qed.

  Definition MonRefInv_body :=
    (∃ M, LocRegister M ∗ [∗ set] l ∈ (dom (gset _) M), l ↦{1/2} -)%I.

  Definition MonRefInv : iProp Σ := inv MonRefN MonRefInv_body.

  Definition MonRefMapsto_def l q v :=
    (MonRefInv ∗ ∃ γ, registered l γ ∗ MonRefFull γ v
                                 ∗ MonRefFrag γ v ∗ l ↦{q /2} v)%I.
  Definition MonRefMapsto_aux l q v : seal (MonRefMapsto_def l q v).
  Proof. by eexists. Qed.
  Definition MonRefMapsto l q v : iProp Σ := (MonRefMapsto_aux l q v).(unseal).
  Definition MonRefMapsto_eq l q v :
    MonRefMapsto l q v = MonRefMapsto_def l q v :=
    (MonRefMapsto_aux l q v).(seal_eq).

  Lemma lookup_register M l γ :
    LocRegister M -∗ registered l γ -∗ ⌜M !! l = Some γ⌝.
  Proof.
    iIntros "Hlv HM".
    iDestruct (own_valid_2 with "Hlv HM") as %[Hv HMv]; simpl in *.
      iPureIntro.
      specialize (Hv O); apply cmra_discrete_included_iff in Hv.
      destruct Hv as [z Hv]; specialize (Hv l). specialize (HMv l).
      revert Hv HMv. rewrite left_id /toRegister lookup_fmap lookup_op.
      intros Hv; rewrite Hv.
      intros HMv. pose proof (cmra_valid_op_r _ _ HMv) as HMv'.
      revert Hv HMv HMv'. case: (z !! l).
      - intros a Hv HMv HMv'.
        destruct (to_agree_uninj _ HMv') as [? Heq].
        revert HMv Hv. rewrite -Heq lookup_singleton; intros HMv Hv.
        apply agree_op_invL' in HMv; subst.
        revert Hv. rewrite -Some_op agree_idemp.
        case (M !! l); simpl; last by inversion 1.
        intros ? HMv.
        by apply Some_equiv_inj, @to_agree_inj, leibniz_equiv in HMv; subst.
      - rewrite right_id lookup_singleton.
        case (M !! l); simpl; last by inversion 1.
        intros ? HMv.
        by apply Some_equiv_inj, @to_agree_inj, leibniz_equiv in HMv; subst.
  Qed.

  Lemma MonRefInv_body_lookup l γ :
    registered l γ -∗ MonRefInv_body -∗
      l ↦{1/2} - ∗ ((l ↦{1/2} -) -∗ MonRefInv_body).
  Proof.
    iIntros "#Hlv Hbd"; iDestruct "Hbd" as (M) "[HM Hreg]".
    iDestruct (lookup_register with "HM Hlv") as %?.
    rewrite (big_sepS_elem_of_acc _ _ l); last by apply elem_of_dom; eauto.
    iDestruct "Hreg" as "[$ Hreg]".
    iIntros "Hl".
    iExists _; iFrame.
    by iApply "Hreg".
  Qed.

  Lemma MonRef_update γ v w a b :
    to_A v = Some a → to_A w = Some b → R a b →
    MonRefFull γ v ==∗ MonRefFull γ w ∗ MonRefFrag γ w.
  Proof.
    iIntros (Hv Hw HR) "HF".
    iDestruct "HF" as (c Hc) "HF"; simplify_eq.
    iMod (own_update _ _ (● Some (principal R b) ⋅ ◯ Some (principal R b))
            with "HF") as "[HF Hf]".
    { apply auth_update_alloc.
      apply local_update_discrete => mz _ HM.
      split; first done.
      destruct mz as [[|]|]; try done.
      rewrite /= -Some_op; f_equiv.
      rewrite /= left_id_L in HM; apply Some_equiv_inj in HM; setoid_subst.
      rewrite (comm op); rewrite principal_op; auto. }
    iModIntro; iSplitL "HF"; iExists _; iSplit; eauto.
  Qed.

  Lemma Register_loc l v a M :
    to_A v = Some a → M !! l = None →
    LocRegister M ==∗ ∃ γ, LocRegister (<[l := γ ]>M) ∗ registered l γ ∗
                           MonRefFull γ v ∗ MonRefFrag γ v.
  Proof.
    iIntros (Hv Hl) "HM".
    iMod (own_alloc (● (Some (principal R a)) ⋅ (◯ (Some (principal R a)))))
      as (γ) "[HFl HFr]"; first done.
    iMod (own_update _ _ (● toRegister (<[l := γ ]>M) ⋅ ◯ {[l := to_agree γ]})
            with "HM") as "[HM Hreg]".
    { apply auth_update_alloc. rewrite /toRegister fmap_insert.
      apply @alloc_singleton_local_update; last done.
      by rewrite lookup_fmap Hl. }
    iModIntro; iExists _; iFrame.
    by iSplit; iExists _; iFrame.
  Qed.

  Lemma MonRefAlloc E l v a :
    nclose MonRefN ⊆ E → to_A v = Some a →
    MonRefInv -∗ l ↦ v ={E}=∗ MonRefMapsto l 1 v.
  Proof.
    iIntros (HE Hv) "#Hinv Hl".
    iInv MonRefN as (M) ">[HM Hpts]" "Hcl".
    iAssert (⌜M !! l = None⌝)%I with "[Hl Hpts]" as %?.
    { destruct (M !! l) as [x|] eqn:Hx; auto.
      iDestruct (big_sepS_elem_of_acc  _ _ l with "Hpts") as "[Hpt _]";
        first by apply elem_of_dom; eauto.
      iDestruct "Hpt" as (w) "[Hpt _]".
      by iDestruct (@mapsto_valid_2 with "Hl Hpt") as "%". }
    iMod (Register_loc with "HM") as (γ) "(HM & Hreg & HFl & HFr)"; eauto.
    iDestruct "Hl" as "[Hl1 Hl2]".
    iMod ("Hcl" with "[HM Hpts Hl1]") as "_".
    { iNext. iExists _; iFrame "HM".
      rewrite dom_insert_L big_sepS_insert; last by apply not_elem_of_dom.
      iFrame; eauto. }
    iModIntro.
    rewrite MonRefMapsto_eq /MonRefMapsto_def. iFrame "#"; iExists _; iFrame.
  Qed.

  Lemma wp_Create_MonRef E (v : val) :
    nclose MonRefN ⊆ E →
    {{{ MonRefInv ∗ ∃ a, ⌜to_A v = Some a⌝ }}}
      Alloc v @ E
    {{{l, RET (Lit $ LitLoc l); MonRefMapsto l 1 v }}}.
  Proof.
    iIntros (HE F) "[#HI H] HF". iDestruct "H" as (a) "%".
    iApply wp_fupd.
    wp_alloc l as "Hl".
    iMod (MonRefAlloc with "[] Hl"); eauto.
    by iModIntro; iApply "HF".
  Qed.

  Lemma wp_Read_MonRef E l q (v : val) :
    nclose MonRefN ⊆ E →
    {{{ MonRefMapsto l q v }}}
      ! (Lit $ LitLoc l) @ E
    {{{RET v; MonRefMapsto l q v }}}.
  Proof.
    rewrite MonRefMapsto_eq /MonRefMapsto_def.
    iIntros (HE F) "[#HI H] HF". iDestruct "H" as (γ) "(Hrg & HFl & HFr & Hl)".
    wp_load.
    iApply "HF"; iFrame "#"; iExists _; iFrame.
  Qed.

  Lemma wp_Write_MonRef E l (v w : val) a b :
    nclose MonRefN ⊆ E →
    to_A v = Some a → to_A w = Some b → R a b →
    {{{ MonRefMapsto l 1 v }}}
      (Lit $ LitLoc l) <- w @ E
    {{{RET #(); MonRefMapsto l 1 w }}}.
  Proof.
    rewrite MonRefMapsto_eq /MonRefMapsto_def.
    iIntros (HE Hv Hw HR F) "[#HI H] HF".
    iDestruct "H" as (γ) "(#Hrg & HFl & HFr& Hl)".
    iInv MonRefN as ">HM" "Hcl".
    iDestruct (MonRefInv_body_lookup with "Hrg HM") as "[Hlv HM]".
    iDestruct "Hlv" as (u) "Hlv".
    iDestruct (@mapsto_agree with "Hl Hlv") as %->.
    iCombine "Hl" "Hlv" as "Hl".
    wp_store.
    iDestruct "Hl" as "[Hl Hl']".
    iMod (MonRef_update with "HFl") as "[HFl HFr']"; eauto.
    iMod ("Hcl" with "[HM Hl']") as "_".
    { iNext. iApply "HM". iExists _; iFrame. }
    iModIntro. iApply "HF".
    rewrite MonRefMapsto_eq /MonRefMapsto_def; iFrame "#".
    iExists _; iFrame "#"; iFrame.
  Qed.

  Lemma snap_shot l q v : MonRefMapsto l q v -∗ atleast l v.
  Proof.
    rewrite MonRefMapsto_eq /MonRefMapsto_def atleast_eq /atleast_def.
    iIntros "[#Hinv Hpt]".
    iDestruct "Hpt" as (γ) "(?&?&?&?)"; iExists _; iFrame.
  Qed.

  Lemma recall l q v w :
    atleast l w -∗ MonRefMapsto l q v -∗
            ∃ a b, ⌜to_A w = Some a ∧ to_A v = Some b ∧ R a b⌝.
  Proof.
    rewrite MonRefMapsto_eq /MonRefMapsto_def atleast_eq /atleast_def.
    iIntros "Hal [#Hinv Hpt]".
    iDestruct "Hpt" as (γ) "(#Hrg1&HFl&HFr&?)".
    iDestruct "Hal" as (γ') "(#Hrg2&HFr')".
    iDestruct (registered_agree with "Hrg1 Hrg2") as %->.
    iApply (MonRef_related with "HFl HFr'").
  Qed.

End MonRef.

Lemma MonRefG_alloc E {A : ofeT} {R : relation A} `{!ProperPreOrder R}
      `{!heapG Σ, !MonRefPreG Σ} :
  (|={E}=> ∃ _ : MonRefG R Σ, MonRefInv R)%I.
Proof.
  iIntros "".
  iMod (own_alloc (A := (authUR (gmapUR loc (agreeR (leibnizC gname)))))
                  (● ∅)) as (γ) "?"; first done.
  iMod (inv_alloc _ _ with "[-]") as "?";
    last by iExists {| MonRefIG_register_name := γ |}; iFrame.
  iNext. iExists ∅.
  rewrite /MonRefInv /MonRefInv_body /LocRegister /toRegister.
  rewrite fmap_empty dom_empty_L big_sepS_empty; iFrame.
Qed.
