From iris.algebra Require Import auth gset.
From iris.base_logic Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.proofmode Require Import tactics.
From iris_monotone Require Import monotone.
From stdpp Require Import relations.


Definition Event : Set := nat * nat.

Definition val_of_event (e : Event) : val := (#e.1, #e.2).

(* Two dummy values for events. *)
Definition event0 : Event := (0, 10).
Definition event1 : Event := (1, 11).

Definition mk_list : val := λ: <>, NONE.

Definition list_add : val :=
  λ: "l" "x", SOME ("x", "l").

Definition list_find : val :=
  rec: "f" "cond" "l" :=
    match: "l" with
      NONE => NONE
    | SOME "x" => if: "cond" (Fst "x") then SOME (Fst "x") else "f" "cond" (Snd "x")
    end.

Definition simulate_receive : val :=
  λ: "dbp" "x",
  (rec: "f" <> :=
     let: "db" := !"dbp" in
     let: "db'" := ref (list_add (!"db") "x") in
     if: CAS "dbp" "db" "db'" then #() else
       "f" #()) #().

Definition is_observed : val :=
  λ: "dbp" "x",
  let: "idx" := Fst "x" in
  let: "db" := !"dbp" in
  let: "l" := !"db" in
  let: "observe" :=
     rec: "f" "i" :=
       match: list_find (λ: "z", Fst "z" = "i") "l" with
         NONE => #false
       | SOME "z" =>
         if: "i" = "idx" then Snd "x" = Snd "z" else "f" ("i" + #1)
       end
  in
  "observe" #0.

Definition wait_observe : val :=
  λ: "dbp" "e",
  (rec: "f" <> := if: is_observed "dbp" "e" then #() else "f" #()) #().

Definition prog : expr :=
  let: "db" := ref (mk_list #()) in
  let: "dbp" := ref "db" in
  Fork (simulate_receive "dbp" (val_of_event event0));;
  Fork (simulate_receive "dbp" (val_of_event event1));;
  wait_observe "dbp" (val_of_event event1);;
  if: is_observed "dbp" (val_of_event event0) then #() else #() #().

Definition STO := gsetO Event.

Definition causally_closed_subset (f g : STO) : Prop :=
  f ⊆ g ∧ ∀ a b, a ∈ g → b ∈ g → a.1 ≤ b.1 → b ∈ f → a ∈ f.

Lemma causally_closed_subset_refl f : causally_closed_subset f f.
Proof. unfold causally_closed_subset; set_solver. Qed.

Lemma causally_closed_subset_trans f g h :
  causally_closed_subset f g →
  causally_closed_subset g h →
  causally_closed_subset f h.
Proof. unfold causally_closed_subset; set_solver. Qed.

Instance: ProperPreOrder causally_closed_subset.
Proof.
  split; first split.
  - intros ?; apply causally_closed_subset_refl.
  - intros ? ? ?; apply causally_closed_subset_trans.
  - intros ? ? ? ->%leibniz_equiv ? ? ->%leibniz_equiv; done.
Qed.

Section verification.
  Context `{!heapG Σ, !inG Σ (authUR (monotoneUR causally_closed_subset))}.

  Fixpoint is_list (l : list Event) (v : val) : Prop :=
    match l with
      [] => v = NONEV
    | (h :: t) => ∃ w, v = SOMEV (val_of_event h, w) ∧ is_list t w
    end.

  Lemma is_list_inj l l' v : is_list l v → is_list l' v → l = l'.
  Proof.
    revert l' v.
    induction l as [|[] l IHl]; intros l' v Hl Hl'.
    - destruct l'; first done.
      destruct Hl' as (?&->&?).
      inversion Hl.
    - destruct Hl as (?&->&?).
      destruct l' as [|[] ?]; first by inversion Hl'.
      destruct Hl' as (?&?&?).
      simplify_eq/=.
      erewrite IHl; eauto.
  Qed.

  Lemma wp_mk_list : {{{ True }}} mk_list #() {{{v, RET v; ⌜is_list [] v⌝ }}}.
  Proof.
    unfold mk_list.
    iIntros (Φ) "_ HΦ"; wp_pures; iApply "HΦ"; auto.
  Qed.

  Lemma wp_list_add a w :
    {{{ True }}}
      list_add w (val_of_event a)
    {{{RET (SOMEV (val_of_event a,w)); True }}}.
  Proof.
    iIntros (Φ) "% HΦ".
    unfold list_add.
    wp_pures.
    iApply "HΦ"; simpl; eauto.
  Qed.

  Lemma wp_list_find (cond : val) (fcond : Event → bool) l w :
    {{{ ⌜is_list l w⌝ ∗
         (∀ a, {{{ True }}} cond (val_of_event a) {{{ RET #(fcond a); True }}}) }}}
      list_find cond w
    {{{ v, RET v;
        (⌜v = NONEV⌝ ∗ ∀ a, ⌜a ∈ l⌝ → ⌜fcond a = false⌝) ∨
        (∃ a, ⌜a ∈ l ∧ fcond a = true⌝ ∗ ⌜v = SOMEV (val_of_event a)⌝) }}}.
  Proof.
    iIntros (Φ) "[Hl #Hcond] HΦ".
    iDestruct "Hl" as %Hl.
    unfold list_find.
    iLöb as "IH" forall (l w Hl).
    wp_pures.
    destruct l as [|a l].
    { simplify_eq/=. wp_pures.
      iApply "HΦ".
      iLeft.
      iModIntro. 
      iSplit; first done.
      iIntros (?); iPureIntro; set_solver. }
    destruct Hl as (u& ->&Hl).
    wp_pures.
    wp_apply "Hcond"; first done.
    iIntros "_".
    destruct (fcond a) eqn:Hfca.
    - wp_pures.
      iApply "HΦ".
      iRight.
      iModIntro.
      iExists a; iSplit; last done.
      iPureIntro; set_solver.
    - do 2 wp_pure _.
      iApply "IH"; first done.
      iNext.
      iIntros (v) "H".
      iApply "HΦ".
      iDestruct "H" as "[[-> H]|H]".
      + iLeft. iSplit; first done.
        iIntros (b [->|]%elem_of_cons); first done.
        iApply "H"; done.
      + iRight.
        iDestruct "H" as (b) "[[% %] %]".
        iExists b; eauto with set_solver.
  Qed.

  Definition observed_everythig_before (l : list Event) (t : nat) :=
    ∀ i, i < t → Exists (λ e, e.1 = i) l.

  Lemma observed_everythig_before_0 l : observed_everythig_before l 0.
  Proof. intros ? ?; lia. Qed.

  Lemma observed_everythig_before_cons e l t :
    observed_everythig_before l t → observed_everythig_before (e :: l) t.
  Proof. unfold observed_everythig_before; naive_solver. Qed.

  Lemma observed_everythig_before_le l t t' :
    t' ≤ t →
    observed_everythig_before l t → observed_everythig_before l t'.
  Proof.
    unfold observed_everythig_before.
    intros Hle Ht i Hi.
    apply Ht; lia.
  Qed.

  Instance observed_everythig_before_dec l t :
    Decision (observed_everythig_before l t).
  Proof.
    unfold observed_everythig_before.
    induction t.
    { left; lia. }
    destruct IHt as [Ht|nHt].
    - destruct (decide (Exists (λ e', e'.1 = t) l)) as [Hl|nHl].
      + left.
        intros i Hi.
        destruct (decide (i = t)) as [->|]; first done.
        apply Ht; lia.
      + right.
        intros Hn; apply nHl.
        apply Hn; lia.
    - right.
      intros Hnt.
      apply nHt; intros; apply Hnt; lia.
  Qed.

  Definition observed_list (l : list Event) : list Event :=
    filter (λ x, observed_everythig_before l (x.1)) l.

  Definition list_to_gset (l : list Event) : gset Event :=
    fold_right (λ e g, {[e]} ∪ g) ∅ l.

  Lemma list_to_gset_equiv l e : e ∈ l ↔ e ∈ list_to_gset l.
  Proof. revert e; induction l as [|e l IHl]; simpl; set_solver. Qed.

  Definition observed (l : list Event) : gset Event :=
    list_to_gset (observed_list l).

  Lemma observed_cons l e :
    (∀ e', e' ∈ l → e.1 = e'.1 → e' = e) →
    causally_closed_subset (observed l) (observed (e :: l)).
  Proof.
    intros He.
    unfold observed.
    split.
    - intros e'.
      rewrite -!list_to_gset_equiv /observed_list !elem_of_list_filter.
      intros [? ?].
      split; first apply observed_everythig_before_cons; set_solver.
    - intros a b.
      rewrite -!list_to_gset_equiv /observed_list !elem_of_list_filter.
      intros [? Ha] [? Hb] ? [Hlb Hbl].
      split.
      eapply observed_everythig_before_le; eauto.
      apply elem_of_cons in Ha as [->|]; last done.
      apply elem_of_cons in Hb as [->|]; first done.
      destruct (decide (e.1 = b.1)).
      { rewrite -(He b); auto. }
      specialize (Hlb e.1).
      revert Hlb; rewrite Exists_exists.
      intros (e' & He'1 & He'2); first lia.
      rewrite -(He e'); auto.
  Qed.

  Lemma in_observed l e :
    e ∈ observed l ↔ e ∈ l ∧ observed_everythig_before l e.1.
  Proof.
    rewrite -!list_to_gset_equiv /observed_list !elem_of_list_filter;
      naive_solver.
  Qed.

  Lemma before_in_observed l e t :
    t ≤ e.1 →
    e ∈ observed l → ∃ e', e' ∈ observed l ∧ e'.1 = t.
  Proof.
    intros Ht.
    destruct (decide (t = e.1)) as [->|].
    { eexists; eauto. }
    rewrite -!list_to_gset_equiv /observed_list !elem_of_list_filter.
    intros [Hel1 Hel2].
    pose proof (Hel1 t) as Hel1'; revert Hel1'.
    rewrite Exists_exists; intros (e'&He'1&He'2); first lia.
    exists e'; split; last done.
    rewrite -!list_to_gset_equiv /observed_list !elem_of_list_filter.
    split; last done.
    eapply observed_everythig_before_le; last done; lia.
  Qed.

  Definition observed_full (γ : gname) (f : STO) :=
    own γ (● principal causally_closed_subset f).

  Definition observed_frag (γ : gname) (f : STO) :=
    own γ (◯ principal causally_closed_subset f).

  Definition db_contents (db : loc) (l : list Event) : iProp Σ :=
    ∃ w q, db ↦{#q} w ∗ ⌜is_list l w⌝.

  Lemma db_contents_duplicable db l :
    db_contents db l ⊢ db_contents db l ∗ db_contents db l.
  Proof.
    unfold db_contents.
    iDestruct 1 as (w q) "[[Hdb1 Hdb2] #Hl]".
    iSplitL "Hdb1"; iExists _; iFrame "#"; iExists _; iFrame.
  Qed.

  Definition inv_name : namespace := nroot .@ "inv".

  Definition observe_inv (γ : gname) (dbp : loc) : iProp Σ :=
    ∃ (db : loc) l,
      dbp ↦ #db ∗ db_contents db l ∗
      ⌜∀ a, a ∈ l → a = event0 ∨ a = event1⌝ ∗
      observed_full γ (observed l).

  Lemma event1_observed_event0_observed E γ dbp f :
    ↑inv_name ⊆ E →
    event1 ∈ f →
    inv inv_name (observe_inv γ dbp) -∗ observed_frag γ f ={E}=∗ ⌜event0 ∈ f⌝.
  Proof.
    iIntros (? He1) "#Hinv #Hf".
    iInv inv_name as (db l) "(Hdbp & >Hdb & >Hl & >Hfl)".
    iDestruct "Hl" as %Hl.
    iDestruct (db_contents_duplicable with "Hdb") as "[Hdb Hdb']".
    iDestruct "Hdb'" as (w q) "[Hdbpt _]".
    iDestruct (own_valid_2 with "Hfl Hf")
      as %[Hf _]%auth_both_valid_discrete.
    revert Hf; rewrite principal_included; intros Hf.
    iModIntro.
    iSplitL.
    { iNext; iExists _, _; iFrame; auto. }
    iModIntro.
    iPureIntro.
    destruct Hf as [Hf1 Hf2].
    eapply (Hf2 _ event1); [|by apply Hf1|simpl; lia|done].
    destruct (before_in_observed l event1 0) as (e' & He'1 & He'2);
      [simpl; lia|by apply Hf1|].
    pose proof He'1 as [[|]%Hl ?]%in_observed; simplify_eq/=; done.
  Qed.

  Lemma wp_simulate_receive γ dbp e :
    e = event0 ∨ e = event1 →
    {{{ inv inv_name (observe_inv γ dbp) }}}
      simulate_receive #dbp (val_of_event e)
    {{{ RET #(); True }}}.
  Proof.
    unfold simulate_receive.
    iIntros (He Φ) "#Hinv HΦ".
    do 4 wp_pure _.
    iLöb as "IH".
    wp_pures.
    wp_bind (! _)%E.
    iInv inv_name as (db l) "(Hdbp & Hdb & >Hl & Hfl)".
    iDestruct "Hl" as %Hl.
    wp_load.
    iDestruct (db_contents_duplicable with "Hdb") as "[Hdb Hdb']".
    iDestruct "Hdb'" as (w q) "[Hdbpt %]".
    iModIntro.
    iSplitL "Hdbp Hdb Hfl".
    { iNext; iExists _, _; iFrame; done. }
    wp_pures.
    wp_load.
    wp_apply wp_list_add; first done.
    iIntros "_".
    wp_alloc newdb as "Hnewdb".
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    iInv inv_name as (db' l') "(Hdbp & Hdb' & >% & Hfl)".
    destruct (decide (db = db')) as [->|].
    - wp_cmpxchg_suc.
      iDestruct "Hdb'" as (w' q') "[Hdbpt' %]".
      iDestruct (mapsto_agree with "Hdbpt Hdbpt'") as %->.
      erewrite (is_list_inj l' l); [|done|done].
      iMod (own_update with "Hfl") as "[Hfl _]".
      { apply auth_update_alloc.
        apply monotone_local_update_grow.
        apply (observed_cons _ e).
        intros ? [->| ->]%Hl; destruct He; simplify_eq/=; done. }
      iModIntro.
      iSplitL "Hdbp Hnewdb Hfl".
      { iNext. iExists _, _; iFrame.
        iSplitL; first by iExists _, _; iFrame; simpl; eauto.
        iPureIntro.
        intros ? [->|]%elem_of_cons; auto. }
      wp_pures.
      iApply "HΦ"; done.
    - wp_cmpxchg_fail.
      iModIntro.
      iSplitL "Hdbp Hdb' Hfl".
      { iNext; iExists _, _; iFrame; eauto. }
      do 2 wp_pure _.
      iApply "IH"; done.
  Qed.

  Lemma wp_is_observed γ dbp e f :
    {{{ inv inv_name (observe_inv γ dbp) ∗ observed_frag γ f }}}
      is_observed #dbp (val_of_event e)
    {{{ (b : bool) g, RET #b;
        ⌜f ⊆ g⌝ ∗ observed_frag γ g ∗ if b then ⌜e ∈ g⌝ else ⌜e ∉ g⌝ }}}.
  Proof.
    unfold is_observed.
    iIntros (Φ) "#[Hinv Hf] HΦ".
    wp_pures.
    wp_bind (! _)%E.
    iInv inv_name as (db l) "(Hdbp & Hdb & >Hl & Hfl)".
    iDestruct "Hl" as %Hl.
    wp_load.
    iDestruct (db_contents_duplicable with "Hdb") as "[Hdb Hdb']".
    iDestruct "Hdb'" as (w q) "[Hdbpt %]".
    iDestruct (own_valid_2 with "Hfl Hf")
      as %[Hf _]%auth_both_valid_discrete.
    revert Hf; rewrite principal_included; intros Hf.
    iMod (own_update with "Hfl") as "[Hfl Hfrg]".
    { apply auth_update_alloc.
      apply monotone_local_update_grow; reflexivity. }
    iDestruct "Hfrg" as "#Hfrg".
    iModIntro.
    iSplitL "Hdbp Hdb Hfl".
    { iNext; iExists _, _; iFrame; done. }
    wp_pures.
    wp_load.
    iClear "Hdbpt".
    do 5 wp_pure _.
    change 0%Z with (0 : Z); simpl.
    assert (0%nat ≤ e.1) as He1 by lia.
    pose proof (observed_everythig_before_0 l) as Hl0.
    revert He1 Hl0.
    generalize 0%nat as i; intros i Hi Hli.
    iLöb as "IH" forall (i Hi Hli).
    wp_pures.
    wp_apply (wp_list_find _ (λ e, bool_decide (e.1 = i))).
    { iSplit; first done.
      iIntros (e' Ψ) "!# _ HΨ".
      wp_pures.
      destruct (decide (e'.1 = i)) as [Heq|Hneq].
      - rewrite !bool_decide_eq_true_2; [|repeat f_equal; done|done].
        iApply "HΨ"; done.
      - rewrite !bool_decide_eq_false_2; [iApply "HΨ"; done|naive_solver|done]. }
    iIntros (v) "[[-> Hv]|Hv]".
    - wp_pures.
      iApply ("HΦ" $! _ (observed l)); iFrame "#".
      iModIntro. 
      iSplit; first by iPureIntro; apply Hf.
      iIntros (He).
      destruct (before_in_observed l e i) as (e' & He'1 & He'2); [done|done|].
      iSpecialize ("Hv" $! e' with "[]"); first by iPureIntro; apply in_observed.
      rewrite bool_decide_eq_true_2; last done.
      iDestruct "Hv" as %?; done.
    - iDestruct "Hv" as (e') "[He'1 ->]".
      wp_pures.
      destruct (decide (i = e.1)) as [Heq|Hneq].
      + rewrite [bool_decide (#i = #e.1)]bool_decide_eq_true_2;
          last naive_solver.
        wp_pures.
        iApply ("HΦ" $! _ (observed l)); iFrame "#".
        iModIntro. 
        iSplit; first by iPureIntro; apply Hf.
        iDestruct "He'1" as %[He'1 He'2%bool_decide_eq_true_1].
        destruct (decide (e.2 = e'.2)) as [Heq'|Hneq'].
        * rewrite Heq' bool_decide_eq_true_2; last done.
          destruct e; destruct e'; simplify_eq/=.
          iPureIntro; apply in_observed; done.
        * rewrite bool_decide_eq_false_2; last naive_solver.
          iIntros ([He1 He2]%in_observed).
          apply Hl in He1 as [|]; apply Hl in He'1 as [|]; simplify_eq /=.
      + rewrite [bool_decide (#i = #e.1)]bool_decide_eq_false_2;
          last naive_solver.
        do 2 wp_pure _.
        replace (i + 1)%Z with (i + 1 : Z); last lia.
        iDestruct "He'1" as %[He'1 He'2%bool_decide_eq_true_1].
        iApply "IH"; [by auto with lia| |done].
        iPureIntro.
        intros j Hj.
        destruct (decide (i = j)) as [->|]; last by apply Hli; lia.
        apply Exists_exists; eauto.
  Qed.

  Lemma wp_wait_observe γ dbp e f :
    {{{ inv inv_name (observe_inv γ dbp) ∗ observed_frag γ f }}}
      wait_observe #dbp (val_of_event e)
    {{{ g, RET #(); ⌜f ⊆ g⌝ ∗ observed_frag γ g ∗ ⌜e ∈ g⌝ }}}.
  Proof.
    unfold wait_observe.
    iIntros (Φ) "#[Hinv Hf] HΦ".
    do 4 wp_pure _.
    iLöb as "IH".
    wp_pures.
    wp_apply wp_is_observed; first by iFrame "#".
    iIntros (b g) "(% & Hg & ?)".
    destruct b.
    - wp_pures.
      iApply "HΦ"; eauto.
    - wp_pure _.
      iApply "IH"; done.
  Qed.

  Theorem wp_prog : {{{ True }}} prog {{{RET #(); True}}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    unfold prog.
    wp_apply wp_mk_list; first done.
    iIntros (v Hv).
    wp_alloc db as "Hdb".
    wp_pures.
    wp_alloc dbp as "Hdbp".
    wp_pures.
    iMod (own_alloc (● principal causally_closed_subset ∅ ⋅
                     ◯ principal causally_closed_subset ∅)) as (γ) "[Hfl #Hfr]".
    { apply auth_both_valid_discrete; done. }
    iMod (inv_alloc inv_name _ (observe_inv γ dbp) with "[Hdb Hdbp Hfl]")
      as "#Hinv".
    { iNext.
      iExists _, []; iFrame.
      iSplitL; first by iExists _, _; iFrame.
      iPureIntro; set_solver. }
    wp_apply wp_fork.
    { iApply wp_simulate_receive; eauto. }
    wp_pures. 
    wp_apply wp_fork.
    { iApply wp_simulate_receive; eauto. }
    wp_pures.
    wp_apply wp_wait_observe; first by iFrame "#".
    iIntros (g) "(_ & #Hg & He1g)".
    iDestruct "He1g" as %He1g.
    wp_pures.
    wp_apply (wp_is_observed _ _ _ g); first by iFrame "#".
    iIntros (b h) "(Hgh & #Hh & Hb)".
    iDestruct "Hgh" as %Hgh.
    iMod (event1_observed_event0_observed with "Hinv Hh") as %?;
      [done|by apply Hgh|].
    destruct b.
    - wp_pures. iApply "HΦ"; done.
    - iDestruct "Hb" as %?; done.
  Qed.

End verification.
