From Coq.Unicode Require Import Utf8.
From Coq.Program Require Import Tactics.
From Coq.micromega Require Import Lia.
From Categories.Essentials Require Import Notations Facts_Tactics Quotient.
From Categories Require Import Category.Main Functor.Main.
From cat_monotone Require Import PartialOrder Lattice PCM.
From Coq.Lists Require Import List.

Section monotone.
  Context (po : PO).

  Definition monotone_base := list po.

  Implicit Types x y z : po.
  Implicit Types a b c : monotone_base.

  Definition principal_base (x : po) : monotone_base := cons x nil.

  Definition monotone_base_op (x y : monotone_base) : monotone_base := x ++ y.

  Definition upper_bound (a : monotone_base) (x : po) := ∀ y, In y a → po y x.

  Definition monotone_rel_base (a b : monotone_base) : Prop :=
    ∀ x, upper_bound a x ↔ upper_bound b x.

  Lemma monotone_rel_base_refl a : monotone_rel_base a a.
  Proof.
    intros x; tauto.
  Qed.

  Lemma monotone_rel_base_symm a b :
    monotone_rel_base a b → monotone_rel_base b a.
  Proof.
    intros Hab x; specialize (Hab x); tauto.
  Qed.

  Lemma monotone_rel_base_trans a b c :
    monotone_rel_base a b → monotone_rel_base b c → monotone_rel_base a c.
  Proof.
    intros Hab Hbc x; specialize (Hab x); specialize (Hbc x); tauto.
  Qed.

  Program Definition monotone_rel : EquiRel monotone_base :=
    {| EQR_rel := monotone_rel_base |}.
  Next Obligation.
  Proof.
    split.
    - intros ?; apply monotone_rel_base_refl.
    - intros ? ?; apply monotone_rel_base_symm.
    - intros ? ? ?; apply monotone_rel_base_trans.
  Qed.

  Definition monotone := quotient monotone_rel.

  Implicit Types A B C : monotone.

  Definition principal (x : po) := class_of monotone_rel (principal_base x).

  Definition monotone_unit := class_of monotone_rel nil.

  Definition monotone_op (x y : monotone) : monotone :=
    class_of
      monotone_rel
      (monotone_base_op (representative x) (representative y)).

  (* Lemma in_monotone_op x a b : *)
  (*   In x (representative (monotone_op a b)) → *)
  (*   (∃ y, In y (representative a) ∧ po x y) ∨ *)
  (*   (∃ y, In y (representative b) ∧ po x y). *)
  (* Proof. *)
  (*   intros Hx. *)
  (*   pose proof (representative_of_class_of monotone_rel *)
  (*                (monotone_base_op (representative a) (representative b))) *)
  (*     as Hab. *)
  (*   specialize (Hab x) as [(z & Hz1 & Hz2) _]. *)
  (*   { eexists; split; [apply Hx| reflexivity]. } *)
  (*   setoid_rewrite in_app_iff in Hz1. *)
  (*   destruct Hz1 as [Hz1|Hz1]; eauto. *)
  (* Qed. *)

  (* Lemma in_monotone_op_back1 x a b : *)
  (*   In x (representative a) → *)
  (*   ∃ y, In y (representative (monotone_op a b)) ∧ po x y. *)
  (* Proof. *)
  (*   intros Hx. *)
  (*   pose proof (representative_of_class_of monotone_rel *)
  (*                (monotone_base_op (representative a) (representative b))) *)
  (*     as Hab. *)
  (*   specialize (Hab x) as [_ (z & Hz1 & Hz2)]. *)
  (*   { setoid_rewrite in_app_iff. *)
  (*     exists x; split; [left; trivial| reflexivity]. } *)
  (*   exists z; auto. *)
  (* Qed. *)

  (* Lemma in_monotone_op_back2 x a b : *)
  (*   In x (representative b) → *)
  (*   ∃ y, In y (representative (monotone_op a b)) ∧ po x y. *)
  (* Proof. *)
  (*   intros Hx. *)
  (*   pose proof (representative_of_class_of monotone_rel *)
  (*                (monotone_base_op (representative a) (representative b))) *)
  (*     as Hab. *)
  (*   specialize (Hab x) as [_ (z & Hz1 & Hz2)]. *)
  (*   { setoid_rewrite in_app_iff. *)
  (*     exists x; split; [right; trivial| reflexivity]. } *)
  (*   exists z; auto. *)
  (* Qed. *)

  (* Lemma monotone_rel_base_nil x : monotone_rel_base nil x → x = nil. *)
  (* Proof. *)
  (*   destruct x as [|a x]; [trivial; fail|]. *)
  (*   intros [_ (? & ? & ?)]. *)
  (*   { exists a; split; [left; trivial| reflexivity]. } *)
  (*   simpl in *; tauto. *)
  (* Qed. *)

  (* Lemma monotone_unit_empty : (representative monotone_unit) = nil. *)
  (* Proof. *)
  (*   assert (∀ x, ¬ In x (representative monotone_unit)) as Hnin. *)
  (*   { intros x Hx. *)
  (*     pose proof (representative_of_class_of monotone_rel nil) as Hnil. *)
  (*     symmetry in Hnil; apply monotone_rel_base_nil in Hnil. *)
  (*     unfold monotone_unit in Hx. *)
  (*     rewrite Hnil in Hx; simpl in *; tauto. } *)
  (*   destruct (representative monotone_unit) as [|a l] eqn:Heq; [trivial|]. *)
  (*   exfalso; apply (Hnin a); left; trivial. *)
  (* Qed. *)

  (* Lemma is_in_monotone_preresntative_class_of x a : *)
  (*   In x a → ∃ y, In y (representative (class_of monotone_rel a)) ∧ po x y. *)
  (* Proof. *)
  (*   intros Hx. *)
  (*   apply (representative_of_class_of monotone_rel a). *)
  (*   eexists; split; [|reflexivity]; trivial. *)
  (* Qed. *)

  (* Lemma in_monotone_preresntative_class_of x a : *)
  (*   In x (representative (class_of monotone_rel a)) → ∃ y, In y a ∧ po x y. *)
  (* Proof. *)
  (*   intros Hx. *)
  (*   apply (representative_of_class_of monotone_rel a). *)
  (*   eexists; split; [|reflexivity]; trivial. *)
  (* Qed. *)

  (* Lemma in_principal x y : In x (representative (principal y)) → po x y. *)
  (* Proof. *)
  (*   intros Hy. *)
  (*   pose proof (representative_of_class_of monotone_rel (principal_base y) x) *)
  (*     as [(z & Hz1 & Hz2) _]. *)
  (*   { exists x; split; [trivial|reflexivity]. } *)
  (*   apply in_inv in Hz1 as [<-|?%in_nil]; tauto. *)
  (* Qed. *)

  (* Lemma is_in_principal x : ∃ y, In y (representative (principal x)) ∧ po x y. *)
  (* Proof. *)
  (*   destruct (representative_represented _ (principal x) x) as *)
  (*       [(z & Hz1 & H2) _]; [|eauto; fail]. *)
  (*   exists x; split; simpl; [auto|reflexivity]. *)
  (* Qed. *)

  Lemma upper_bound_representative_of_class_of a x :
    upper_bound (representative (class_of monotone_rel a)) x ↔ upper_bound a x.
  Proof.
    apply (representative_of_class_of monotone_rel a).
  Qed.

  Lemma upper_bound_monotone_op_fold A B x :
    upper_bound (monotone_base_op (representative A) (representative B)) x ↔
    upper_bound (representative (monotone_op A B)) x.
  Proof.
    unfold monotone_op.
    rewrite upper_bound_representative_of_class_of; tauto.
  Qed.

  Lemma upper_bound_monotone_op A B x :
    (upper_bound (representative (monotone_op A B)) x) ↔
    (upper_bound (representative A) x) ∧
    (upper_bound (representative B) x).
  Proof.
    unfold monotone_op.
    rewrite upper_bound_representative_of_class_of.
    split.
    - intros Ha.
      split.
      + intros b Hb; apply Ha; apply in_or_app; auto.
      + intros b Hb; apply Ha; apply in_or_app; auto.
    - intros [Ha1 Ha2].
      intros b Hb; apply in_app_or in Hb.
      destruct Hb as [Hb|Hb]; [apply Ha1|apply Ha2]; auto.
  Qed.

  Lemma upper_bound_unit x : upper_bound (representative monotone_unit) x.
  Proof.
    apply upper_bound_representative_of_class_of.
    intros ? ?; simpl in *; tauto.
  Qed.

  Lemma monotone_op_comm A B : monotone_op A B = monotone_op B A.
  Proof.
    apply class_of_inj.
    intros c.
    rewrite !upper_bound_monotone_op_fold, !upper_bound_monotone_op; tauto.
  Qed.

  Lemma monotone_op_assoc A B C :
    monotone_op (monotone_op A B) C = monotone_op A (monotone_op B C).
  Proof.
    apply class_of_inj.
    intros c.
    rewrite !upper_bound_monotone_op_fold, !upper_bound_monotone_op; tauto.
  Qed.

  Lemma monotone_op_unit_id A : monotone_op monotone_unit A = A.
  Proof.
    apply (uniquely_represented _ _ _ (representative A) (representative A));
    [|apply representative_represented|reflexivity].
    apply (related_represented
             _ _ (representative (monotone_op monotone_unit A))).
    { apply representative_represented. }
    intros c.
    rewrite !upper_bound_monotone_op.
    split; [tauto|].
    - split; [|tauto].
      apply upper_bound_unit.
  Qed.

  Lemma monotone_op_idemp A : monotone_op A A = A.
  Proof.
    eapply uniquely_represented;
      [apply representative_represented|apply representative_represented|].
    intros c.
    rewrite !upper_bound_monotone_op; tauto.
  Qed.

  Definition monotone_order A B := ∃ C, B = monotone_op A C.

  Local Obligation Tactic := idtac.

  Program Definition monotone_order_PO : PO :=
    {| PO_type := monotone;
       PO_car := monotone_order
    |}.
  Next Obligation.
  Proof.
    split.
    - intros x; exists monotone_unit.
      rewrite monotone_op_comm, monotone_op_unit_id; trivial.
    - intros x y z [u Hu] [v Hv].
      exists (monotone_op u v).
      rewrite Hv, Hu, monotone_op_assoc; trivial.
  Qed.
  Next Obligation.
  Proof.
    intros x y [z ->] [u ->].
    rewrite !monotone_op_assoc.
    rewrite (monotone_op_comm z (monotone_op _ _)).
    rewrite !monotone_op_assoc.
    rewrite monotone_op_idemp.
    rewrite (monotone_op_comm z); trivial.
  Qed.

  Program Definition monotone_JSLB : JSLB :=
    {| JSLB_PO := monotone_order_PO;
       join := monotone_op;
       bot := monotone_unit; |}.
  Next Obligation.
  Proof.
    intros x; exists x; rewrite monotone_op_unit_id; trivial.
  Qed.
  Next Obligation.
  Proof.
    intros x y; exists y; trivial.
  Qed.
  Next Obligation.
  Proof.
    intros x y; exists x; rewrite monotone_op_comm; trivial.
  Qed.
  Next Obligation.
  Proof.
    intros x y z [u Hxz] [v Hyz]; simpl in *.
    exists (monotone_op u v).
    rewrite (monotone_op_comm u v).
    rewrite (monotone_op_assoc x).
    rewrite <- (monotone_op_assoc y).
    rewrite <- Hyz.
    rewrite (monotone_op_comm z u).
    rewrite <- (monotone_op_assoc x).
    rewrite <- Hxz.
    rewrite monotone_op_idemp; trivial.
  Qed.

  Lemma monotone_correct x y :
    po x y ↔ monotone_order (principal x) (principal y).
  Proof.
    split.
    - intros Hxy.
      exists (principal y).
      apply class_of_inj.
      intros c.
      rewrite !upper_bound_monotone_op_fold, !upper_bound_monotone_op.
      unfold principal.
      rewrite !upper_bound_representative_of_class_of.
      split.
      + intros Hc.
        split; [|tauto].
        intros ? [<-|]; simpl in *; [|tauto].
        transitivity y; [assumption|].
        eapply Hc; repeat constructor.
      + tauto.
    - intros [C HC].
      assert (monotone_rel
                (principal_base y)
                (monotone_base_op
                   (representative (principal x))
                   (representative C)))
        as Hrel by (apply equal_classes; trivial).
      destruct (Hrel y) as [Hy _].
      rewrite !upper_bound_monotone_op_fold, !upper_bound_monotone_op in Hy.
      destruct Hy as [Hy _].
      { intros ? [<-|]; simpl in *; [reflexivity|tauto]. }
      apply -> upper_bound_representative_of_class_of in Hy.
      apply Hy.
      repeat constructor.
  Qed.

End monotone.

Local Obligation Tactic := idtac.

Program Definition PO_morphism_of_monotone_JSLB_morph
        po po' (f : PO_morphism po po') :
  PO_morphism (monotone_order_PO po) (monotone_order_PO po') :=
{| POM_mor x := class_of (monotone_rel po') (map f (representative x))
|}.
Next Obligation.
Proof.
  intros po po' f x y [u ->]; simpl in *.
  exists (class_of (monotone_rel po') (map f (representative u))).
  apply class_of_inj.
  intros c.
  rewrite upper_bound_monotone_op_fold, upper_bound_monotone_op,
    !upper_bound_representative_of_class_of.
  
  -


  intros c; split; setoid_rewrite in_app_iff.
  - intros (d & Hd1 & Hd2).
    apply in_map_iff in Hd1 as [d' [<- Hd']].
    apply in_monotone_op in Hd' as [(z & Hz1 & Hz2)|(z & Hz1 & Hz2)].
    + destruct (is_in_monotone_preresntative_class_of
                  po' (f z) (map f (representative x)))
        as (w & Hw1 & Hw2).
      { apply in_map; trivial. }
      exists w; split; [left; trivial; fail|].
      transitivity (f d'); [trivial; fail|].
      transitivity (f z); [|trivial; fail].
      apply POM_mono; trivial.
    + destruct (is_in_monotone_preresntative_class_of
                  po' (f z) (map f (representative u)))
        as (w & Hw1 & Hw2).
      { apply in_map; trivial. }
      exists w; split; [right; trivial; fail|].
      transitivity (f d'); [trivial; fail|].
      transitivity (f z); [|trivial; fail].
      apply POM_mono; trivial.
  - intros (d & [Hd1|Hd1] & Hd2).
    + apply in_monotone_preresntative_class_of in Hd1 as (e & He1 & He2).
      apply in_map_iff in He1 as [e' [<- He']].
      apply (in_monotone_op_back1 _ _ _ u) in He' as (i & Hi1 & Hi2).
      exists (f i); split; [apply in_map; trivial; fail|].
      transitivity d; [assumption|].
      transitivity (f e'); [assumption|].
      apply POM_mono; trivial.
    + apply in_monotone_preresntative_class_of in Hd1 as (e & He1 & He2).
      apply in_map_iff in He1 as [e' [<- He']].
      apply (in_monotone_op_back2 _ _ x) in He' as (i & Hi1 & Hi2).
      exists (f i); split; [apply in_map; trivial; fail|].
      transitivity d; [assumption|].
      transitivity (f e'); [assumption|].
      apply POM_mono; trivial.
Qed.

Program Definition monotone_JSLB_morph po po' (f : PO_morphism po po') :
    JSLB_morphism (monotone_JSLB po) (monotone_JSLB po') :=
{| JSLBM_mor := PO_morphism_of_monotone_JSLB_morph po po' f |}.
Next Obligation.
Proof.
  intros po po' f x y; simpl.
  apply class_of_inj.
  intros c; split; setoid_rewrite in_app_iff.
  - intros (d & Hd1 & Hd2).
    apply in_map_iff in Hd1 as [d' [<- Hd']].
    apply in_monotone_op in Hd' as [(z & Hz1 & Hz2)|(z & Hz1 & Hz2)].
    + destruct (is_in_monotone_preresntative_class_of
                  po' (f z) (map f (representative x)))
        as (w & Hw1 & Hw2).
      { apply in_map; trivial. }
      exists w; split; [left; trivial; fail|].
      transitivity (f d'); [trivial; fail|].
      transitivity (f z); [|trivial; fail].
      apply POM_mono; trivial.
    + destruct (is_in_monotone_preresntative_class_of
                  po' (f z) (map f (representative y)))
        as (w & Hw1 & Hw2).
      { apply in_map; trivial. }
      exists w; split; [right; trivial; fail|].
      transitivity (f d'); [trivial; fail|].
      transitivity (f z); [|trivial; fail].
      apply POM_mono; trivial.
  - intros (d & [Hd1|Hd1] & Hd2).
    + apply in_monotone_preresntative_class_of in Hd1 as (e & He1 & He2).
      apply in_map_iff in He1 as [e' [<- He']].
      apply (in_monotone_op_back1 _ _ _ y) in He' as (i & Hi1 & Hi2).
      exists (f i); split; [apply in_map; trivial; fail|].
      transitivity d; [assumption|].
      transitivity (f e'); [assumption|].
      apply POM_mono; trivial.
    + apply in_monotone_preresntative_class_of in Hd1 as (e & He1 & He2).
      apply in_map_iff in He1 as [e' [<- He']].
      apply (in_monotone_op_back2 _ _ x) in He' as (i & Hi1 & Hi2).
      exists (f i); split; [apply in_map; trivial; fail|].
      transitivity d; [assumption|].
      transitivity (f e'); [assumption|].
      apply POM_mono; trivial.
Qed.
Next Obligation.
Proof.
  intros po po' f.
  apply class_of_inj.
  intros x; split.
  - intros (d & Hd1 & Hd2).
    apply in_map_iff in Hd1 as [d' [<- Hd']].
    simpl in Hd'; rewrite monotone_unit_empty in Hd'; simpl in Hd'; tauto.
  - intros (d & [] & Hd2).
Qed.

Program Definition monotone_JSLB_functor : Functor PO_cat JSLB_cat :=
  {| FO := monotone_JSLB;
     FA := monotone_JSLB_morph |}.
Next Obligation.
Proof.
  intros po.
  apply JSLBM_morphism_eq.
  apply POM_morphism_eq.
  intros a; cbn.
  rewrite map_id.
  apply class_of_representative.
Qed.
Next Obligation.
Proof.
  intros po po' po'' f g.
  apply JSLBM_morphism_eq.
  apply POM_morphism_eq.
  intros x; cbn.
  apply class_of_inj.
  intros y; split.
  - intros (z & Hz1 & Hz2).
    apply in_map_iff in Hz1 as (w & <- & Hw2).
    assert (In (f w) (map f (representative x))) as Hfw
        by (apply in_map; trivial).
    apply is_in_monotone_preresntative_class_of in Hfw as (u & Hu1 & Hu2).
    exists (g u); split; [apply in_map; trivial; fail|].
    etransitivity; [eassumption|].
    apply POM_mono; trivial.
  - intros (z & Hz1 & Hz2).
    apply in_map_iff in Hz1 as (w & <- & Hw2).
    apply in_monotone_preresntative_class_of in Hw2 as (u & Hu1 & Hu2).
    apply in_map_iff in Hu1 as (v & <- & Hv2).
    exists (g (f v)); split.
    + apply in_map_iff; eauto.
    + transitivity (g w); [eassumption|].
      apply POM_mono; trivial.
Qed.

(* an example *)

Program Definition nat_le_PO : PO :=
{| PO_car := le |}.

Next Obligation.
Proof.
  lia.
Qed.

Lemma fold_right_max_UB x a : In a x → a ≤ fold_right max 0 x.
Proof.
  induction x as [|b x IHx]; simpl; [tauto|].
  intros [->| Ha]; [|apply IHx in Ha]; lia.
Qed.

Lemma fold_right_max_zeor_or_in x :
  (fold_right max 0 x = 0 ∧ (∀ a, In a x → a = 0)) ∨
  ((fold_right max 0 x) ≠ 0 ∧ In (fold_right max 0 x) x).
Proof.
  induction x as [|a x IHx]; simpl.
  { tauto. }
  destruct IHx as [[-> IHx]|[IHx1 IHx2]].
  + destruct a.
    * left; split; [trivial; fail|].
      intros a [<-|]; auto.
    * rewrite PeanoNat.Nat.max_0_r; auto.
  + destruct (Compare_dec.le_gt_dec a (fold_right Nat.max 0 x)); [|lia].
    right.
    replace (Nat.max a (fold_right Nat.max 0 x)) with (fold_right Nat.max 0 x)
      by lia; auto.
Qed.

Lemma fold_right_max_LUB x a : (∀ b, In b x → b ≤ a) → fold_right max 0 x ≤ a.
Proof.
  induction x as [|b x IHx]; simpl; [lia|].
  intros Ha.
  assert (b ≤ a).
  { apply Ha; auto. }
  assert (fold_right Nat.max 0 x ≤ a).
  { destruct (fold_right_max_zeor_or_in x) as [[-> _]|[? ?]]; [lia|].
    apply Ha; auto. }
  lia.
Qed.

Lemma fold_right_max_of_related_le (x y : monotone_base nat_le_PO) :
  monotone_rel_base nat_le_PO x y →
  fold_right max 0 x ≤ fold_right max 0 y.
Proof.
  intros Hxy.
  apply fold_right_max_LUB.
  intros a Ha.
  destruct (Hxy a) as [(b & Hb1 & Hb2) _].
  { exists a; split; [auto|reflexivity]. }
  transitivity b; [trivial|].
  apply fold_right_max_UB; trivial.
Qed.

Lemma fold_right_max_of_related (x y : monotone_base nat_le_PO) :
  monotone_rel_base nat_le_PO x y →
  fold_right max 0 x = fold_right max 0 y.
Proof.
  intros.
  apply PeanoNat.Nat.le_antisymm.
  - apply fold_right_max_of_related_le; trivial.
  - apply fold_right_max_of_related_le.
    apply monotone_rel_base_symm; trivial.
Qed.

Lemma fold_right_max_of_representative_of_class_of x :
  fold_right max 0 (representative (class_of (monotone_rel nat_le_PO) x)) =
  fold_right max 0 x.
Proof.
  apply fold_right_max_of_related.
  apply (representative_of_class_of (monotone_rel nat_le_PO)).
Qed.

Lemma fold_right_max_app_le_l x y :
  fold_right max 0 x ≤ fold_right max 0 (x ++ y).
Proof. induction x; simpl; lia. Qed.

Lemma fold_right_max_app_le_r x y :
  fold_right max 0 y ≤ fold_right max 0 (x ++ y).
Proof. induction x; simpl; lia. Qed.

Lemma fold_right_max_app x y :
  fold_right max 0 (x ++ y) = max (fold_right max 0 x) (fold_right max 0 y).
Proof.
  apply PeanoNat.Nat.le_antisymm.
  - apply fold_right_max_LUB.
    intros b [Hb|Hb]%in_app_or.
    + etransitivity; [apply (fold_right_max_UB x); trivial|lia].
    + etransitivity; [apply (fold_right_max_UB y); trivial|lia].
  - apply PeanoNat.Nat.max_case_strong.
    + intros; apply fold_right_max_app_le_l.
    + intros; apply fold_right_max_app_le_r.
Qed.

Definition nat_max_monotone_jslb : JSLB := monotone_JSLB nat_le_PO.

Definition nat_max_monotone_pcm : PCM := PCM_of_JSLB nat_max_monotone_jslb.

Program Definition nat_max_to_nat_max_monotone :
  Hom PCM_cat nat_max_pcm nat_max_monotone_pcm :=
  {| PCMM_mor :=
       λ n, match n return monotone nat_le_PO with
              0 => monotone_unit nat_le_PO
            | _ => principal nat_le_PO n
            end |}.

Next Obligation.
Proof.
  trivial.
Qed.
Next Obligation.
Proof.
  intros x y; simpl.
  destruct x as [|x].
  { destruct y as [|y]; simpl.
    - rewrite monotone_op_unit_id; trivial.
    - rewrite monotone_op_unit_id; trivial. }
  destruct y as [|y]; simpl.
  { rewrite monotone_op_comm, monotone_op_unit_id; trivial. }
  apply class_of_inj.
  intros c.
  setoid_rewrite in_app_iff.
  split; simpl.
  - intros (d & Hd1 & Hd2).
    destruct Hd1 as [<-|Hd1]; [|tauto].
    destruct (Compare_dec.le_gt_dec x y).
    + destruct (is_in_principal nat_le_PO (S y)) as (z & Hz1 & Hz2).
      exists z; split; simpl in *; [right; trivial|lia].
    + destruct (is_in_principal nat_le_PO (S x)) as (z & Hz1 & Hz2).
      exists z; split; simpl in *; [left; trivial|lia].
  - intros (d & Hd1 & Hd2).
    destruct Hd1 as [Hd1|Hd1].
    + apply (in_principal nat_le_PO) in Hd1; simpl in *.
      eexists; split; [left; trivial|]; lia.
    + apply (in_principal nat_le_PO) in Hd1; simpl in *.
      eexists; split; [left; trivial|]; lia.
Qed.
Next Obligation.
Proof.
  trivial.
Qed.

Program Definition nat_max_monotone_to_nat_max :
  Hom PCM_cat nat_max_monotone_pcm nat_max_pcm :=
  {| PCMM_mor :=
       λ x, fold_right max 0 (representative x) |}.

Next Obligation.
Proof.
  trivial.
Qed.
Next Obligation.
Proof.
  intros x y; simpl.
  unfold monotone_op.
  rewrite fold_right_max_of_representative_of_class_of.
  unfold monotone_base_op.
  apply fold_right_max_app.
Qed.
Next Obligation.
Proof.
  simpl; rewrite monotone_unit_empty; trivial.
Qed.

Program Definition natx_max_iso :
  (nat_max_pcm ≃≃ nat_max_monotone_pcm ::> PCM_cat)%isomorphism :=
  {| iso_morphism := nat_max_to_nat_max_monotone;
     inverse_morphism := nat_max_monotone_to_nat_max |}.

Next Obligation.
Proof.
  apply PCMM_morphism_eq; simpl.
  intros x.
  destruct x as [|x].
  - rewrite monotone_unit_empty; trivial.
  - unfold principal.
    rewrite fold_right_max_of_representative_of_class_of; trivial.
Qed.
Next Obligation.
Proof.
  apply PCMM_morphism_eq; simpl.
  intros x.
  
