From Coq.Unicode Require Import Utf8.
From Coq.Program Require Import Tactics.
From Categories.Essentials Require Import Facts_Tactics Quotient.
From Categories Require Import
     Essentials.Notations Category.Main Functor.Main Adjunction.Main
     NatTrans.Main.
From Coq.Lists Require Import List.
From cat_monotone Require Import Lattice PartialOrder monotone.

Local Obligation Tactic := idtac.

Program Definition unit_morphism c :
  PO_morphism c (monotone_order_PO c) :=
  {| POM_mor x := principal _ x |}.
Next Obligation.
Proof.
  intros po x y Hxy; cbn.
  apply monotone_correct; trivial.
Qed.

Program Definition unit_of_adjunction :
  ((Functor_id PO_cat) -->
   (JSLB_forgetful_functor ∘ monotone_JSLB_functor))%nattrans :=
{| Trans := unit_morphism |}.
Next Obligation.
Proof.
  intros po po' f; cbn in *.
  apply POM_morphism_eq; cbn.
  intros x.
  apply class_of_inj.
  intros c.
  split.
  - intros (d & Hd1 & Hd2).
    eapply in_inv in Hd1 as [<-|?%in_nil]; [|tauto].
    destruct (is_in_monotone_preresntative_class_of po x (principal_base _ x))
      as (e & He1 & He2).
    { apply in_eq. }
    exists (f e); split.
    + apply in_map; trivial.
    + transitivity (f x); [assumption|].
      apply POM_mono; trivial.
  - intros (d & Hd1 & Hd2).
    apply in_map_iff in Hd1 as (e & <- & He).
    apply in_principal in He.
    exists (f x); split; [apply in_eq|].
    transitivity (f e); [assumption|].
    apply POM_mono; trivial.
Qed.
Next Obligation.
Proof.
  symmetry.
  apply unit_of_adjunction_obligation_1.
Qed.

Definition join_of_list (c : JSLB) (x : list c) : c :=
  fold_right (λ y z, join c y z) (bot c) x.

Lemma join_of_list_UB (c : JSLB) x u : In u x → c u (join_of_list c x).
Proof.
  revert u.
  induction x as [|v x IHx]; intros u Hu; simpl in *.
  { tauto. }
  destruct Hu as [->|Hu]; unfold join_of_list; simpl.
  - apply join_UB1.
  - etransitivity; [|apply join_UB2].
    apply IHx; trivial.
Qed.

Lemma join_of_list_LUB (c : JSLB) x w :
  (∀ u, In u x → c u w) → c (join_of_list c x) w.
Proof.
  revert w.
  induction x as [|v x IHx]; intros u Hu; simpl in *.
  { apply bot_least. }
  apply join_LUB.
  - apply Hu; auto.
  - apply IHx; auto.
Qed.

Lemma join_of_list_preserved c c' (f : JSLB_morphism c c') x :
  f (join_of_list c x) = join_of_list c' (map f x).
Proof.
  induction x as [|u x IHx]; simpl.
  { apply JSLBM_bot. }
  rewrite JSLBM_resp, IHx; trivial.
Qed.

Lemma join_of_list_map_principal (po : PO) (y : list po) :
  join_of_list (monotone_JSLB po) (map (λ z : po, principal po z) y) =
  class_of (monotone_rel po) y.
Proof.
  eapply uniquely_represented;
    [apply representative_represented|apply class_of_represents|].
  induction y as [|u y IHy]; simpl.
  - split; intros (w & Hw1 & Hw2).
    + apply monotone_unit_empty in Hw1; tauto.
    + simpl in *; tauto.
  - split; intros (w & Hw1 & Hw2).
    + apply in_monotone_op in Hw1 as [(v & Hv1 & Hv2)|(v & Hv1 & Hv2)].
      * apply in_principal in Hv1.
        exists u; split; [simpl; auto|].
        transitivity w; [trivial; fail|].
        transitivity v; trivial; fail.
      * edestruct (IHy w) as [(t & Ht1 & Ht2) _]; [eauto; fail|].
        exists t; split; [simpl; auto|].
        transitivity w; auto.
    + destruct Hw1 as [->|Hw1].
      * destruct (is_in_principal _ w) as (u & Hu1 & Hu2).
        eapply in_monotone_op_back1 in Hu1 as (v & Hv1 & Hv2).
        exists v; split; [apply Hv1|].
        transitivity w; [trivial; fail|].
        transitivity u; trivial.
      * edestruct (IHy w) as [_ (v & Hv1 & Hv2)].
        { exists w; split; [|reflexivity]; trivial. }
        eapply in_monotone_op_back2 in Hv1 as (t & Ht1 & Ht2).
        exists t; split; [apply Ht1|].
        transitivity w; auto.
        transitivity v; auto.
Qed.

Lemma join_of_list_representative (c : JSLB) (x : c) :
  join_of_list c (representative (principal c x)) = x.
Proof.
  apply PO_antisymm.
  - apply join_of_list_LUB.
    intros u Hu.
    apply in_principal in Hu; trivial.
  - destruct (is_in_principal c x) as (z & Hz1 & Hz2).
    transitivity z; [trivial; fail|].
    apply join_of_list_UB; auto.
Qed.

Definition join_of (c : JSLB) (x : monotone c) : c :=
  join_of_list c (representative x).

Lemma join_of_class_of (c : JSLB) (x : list c) :
  join_of c (class_of (monotone_rel c) x) = join_of_list c x.
Proof.
  unfold join_of.
  apply PO_antisymm.
  - apply join_of_list_LUB.
    intros u Hu.
    apply in_monotone_preresntative_class_of in Hu as (w & Hw1 & Hw2).
      etransitivity; [apply Hw2|].
      apply join_of_list_UB; trivial.
  - apply join_of_list_LUB.
    intros u Hu.
    apply is_in_monotone_preresntative_class_of in Hu as (w & Hw1 & Hw2).
    etransitivity; [apply Hw2|].
    apply join_of_list_UB; trivial.
Qed.

Lemma join_of_op c x y :
  (join_of c (monotone_op c x y)) = join c (join_of c x) (join_of c y).
Proof.
  unfold join_of.
  apply PO_antisymm.
  - apply join_of_list_LUB.
    intros u Hu.
    apply in_monotone_op in Hu as [(w & Hw1 & Hw2)|(w & Hw1 & Hw2)].
    + etransitivity; [|apply join_UB1].
      etransitivity; [apply Hw2|].
      apply join_of_list_UB; trivial.
    + etransitivity; [|apply join_UB2].
      etransitivity; [apply Hw2|].
      apply join_of_list_UB; trivial.
  - apply join_LUB.
    + apply join_of_list_LUB.
      intros u Hu.
      apply (in_monotone_op_back1 _ _ _ y) in Hu as (w & Hw1 & Hw2).
      etransitivity; [apply Hw2|].
      apply join_of_list_UB; trivial.
    + apply join_of_list_LUB.
      intros u Hu.
      apply (in_monotone_op_back2 _ _ x) in Hu as (w & Hw1 & Hw2).
      etransitivity; [apply Hw2|].
      apply join_of_list_UB; trivial.
Qed.

Lemma join_of_monotone_unit c : join_of c (monotone_unit c) = bot c.
Proof.
  unfold join_of.
  apply PO_antisymm; [|apply bot_least].
  apply join_of_list_LUB.
  intros u Hu.
  apply monotone_unit_empty in Hu; tauto.
Qed.

Lemma join_of_preserved c c' (f : JSLB_morphism c c') x :
  join_of c' (class_of (monotone_rel c') (map f (representative x))) =
  f (join_of c x).
Proof.
  rewrite join_of_class_of.
  unfold join_of.
  rewrite join_of_list_preserved; trivial.
Qed.

Program Definition POM_for_counit_morphism (c : JSLB) :
  PO_morphism (monotone_order_PO c) c :=
{| POM_mor x := join_of c x |}.
Next Obligation.
Proof.
  intros j x y [u ->]; simpl.
  rewrite join_of_op.
  apply join_UB1.
Qed.

Program Definition couni_morphism (c : JSLB) :
  JSLB_morphism (monotone_JSLB c) c :=
{| JSLBM_mor := POM_for_counit_morphism c |}.
Next Obligation.
Proof.
  cbn.
  intros c x y.
  apply join_of_op.
Qed.
Next Obligation.
Proof.
  cbn.
  intros c.
  apply join_of_monotone_unit.
Qed.

Program Definition counit_of_adjunction :
  (monotone_JSLB_functor ∘ JSLB_forgetful_functor -->
   Functor_id JSLB_cat)%nattrans :=
{| Trans := couni_morphism |}.
Next Obligation.
Proof.
  cbn.
  intros j j' f.
  apply JSLBM_morphism_eq.
  apply POM_morphism_eq; cbn.
  intros x.
  apply join_of_preserved.
Qed.
Next Obligation.
Proof.
  cbn.
  intros j j' f.
  apply JSLBM_morphism_eq.
  apply POM_morphism_eq; cbn.
  intros x.
  symmetry.
  apply join_of_preserved.
Qed.

Program Definition monote_left_adjoint_to_extension :
  (monotone_JSLB_functor ⊣_ucu JSLB_forgetful_functor)%functor :=
  {| ucu_adj_unit := unit_of_adjunction;
     ucu_adj_counit := counit_of_adjunction; |}.
Next Obligation.
Proof.
  apply NatTrans_eq_simplify; simpl.
  extensionality po; simpl.
  apply JSLBM_morphism_eq.
  apply POM_morphism_eq.
  intros x; simpl.
  rewrite join_of_class_of.
  rewrite join_of_list_map_principal.
  apply class_of_representative.
Qed.
Next Obligation.
Proof.
  apply NatTrans_eq_simplify; simpl.
  extensionality j; simpl.
  apply POM_morphism_eq.
  intros x; simpl.
  rewrite join_of_class_of.
  rewrite map_id.
  apply join_of_list_representative.
Qed.
