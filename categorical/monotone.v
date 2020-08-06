From Coq.Unicode Require Import Utf8.
From Coq.Program Require Import Tactics.
From Categories.Essentials Require Import Facts_Tactics Quotient.
From Categories Require Import Category.Main Functor.Main.
From cat_monotone Require Import RA PreOrder.
From Coq.Lists Require Import List.

Section monotone.
  Context (po : PO).

  Definition monotone_base := list po.

  Definition principal_base (x : po) : monotone_base := cons x nil.

  Definition monotone_base_op (x y : monotone_base) : monotone_base := x ++ y.

  Definition monotone_rel_base (a b : monotone_base) : Prop :=
    ∀ x, (∃ y, In y a ∧ po x y) ↔ (∃ y, In y b ∧ po x y).

  Program Definition monotone_rel : EquiRel monotone_base :=
    {| EQR_rel := monotone_rel_base |}.
  Next Obligation.
  Proof.
    split.
    - intros a x; tauto.
    - intros a b Hab x; specialize (Hab x); tauto.
    - intros a b c Hab Hbc x; specialize (Hab x); specialize (Hbc x); tauto.
  Qed.

  Definition monotone := quotient monotone_rel.

  Definition principal (x : po) := class_of monotone_rel (principal_base x).

  Definition monotone_unit := class_of monotone_rel nil.

  Definition monotone_op (x y : monotone) : monotone :=
    class_of
      monotone_rel
      (monotone_base_op (representative x) (representative y)).

  Lemma in_monotone_op x a b :
    In x (representative (monotone_op a b)) →
    (∃ y, In y (representative a) ∧ po x y) ∨
    (∃ y, In y (representative b) ∧ po x y).
  Proof.
    intros Hx.
    pose proof (representative_of_class_of monotone_rel
                 (monotone_base_op (representative a) (representative b)))
      as Hab.
    specialize (Hab x) as [(z & Hz1 & Hz2) _].
    { eexists; split; [apply Hx| reflexivity]. }
    setoid_rewrite in_app_iff in Hz1.
    destruct Hz1 as [Hz1|Hz1]; eauto.
  Qed.

  Lemma in_monotone_op_back1 x a b :
    In x (representative a) →
    ∃ y, In y (representative (monotone_op a b)) ∧ po x y.
  Proof.
    intros Hx.
    pose proof (representative_of_class_of monotone_rel
                 (monotone_base_op (representative a) (representative b)))
      as Hab.
    specialize (Hab x) as [_ (z & Hz1 & Hz2)].
    { setoid_rewrite in_app_iff.
      exists x; split; [left; trivial| reflexivity]. }
    exists z; auto.
  Qed.

  Lemma in_monotone_op_back2 x a b :
    In x (representative b) →
    ∃ y, In y (representative (monotone_op a b)) ∧ po x y.
  Proof.
    intros Hx.
    pose proof (representative_of_class_of monotone_rel
                 (monotone_base_op (representative a) (representative b)))
      as Hab.
    specialize (Hab x) as [_ (z & Hz1 & Hz2)].
    { setoid_rewrite in_app_iff.
      exists x; split; [right; trivial| reflexivity]. }
    exists z; auto.
  Qed.

  Lemma monotone_unit_empty x : ¬ In x (representative monotone_unit).
  Proof.
    intros Hx.
    pose proof (representative_of_class_of monotone_rel nil) as Hnil.
    specialize (Hnil x) as [(z & Hz1%in_nil & Hz2) _]; [|trivial; fail].
    exists x; split; [trivial|reflexivity].
  Qed.

  Lemma is_in_monotone_preresntative_class_of x a :
    In x a → ∃ y, In y (representative (class_of monotone_rel a)) ∧ po x y.
  Proof.
    intros Hx.
    apply (representative_of_class_of monotone_rel a).
    eexists; split; [|reflexivity]; trivial.
  Qed.

  Lemma in_monotone_preresntative_class_of x a :
    In x (representative (class_of monotone_rel a)) → ∃ y, In y a ∧ po x y.
  Proof.
    intros Hx.
    apply (representative_of_class_of monotone_rel a).
    eexists; split; [|reflexivity]; trivial.
  Qed.

  Lemma in_principal x y : In x (representative (principal y)) → po x y.
  Proof.
    intros Hy.
   pose proof (representative_of_class_of monotone_rel (principal_base y) x)
      as [(z & Hz1 & Hz2) _].
    { exists x; split; [trivial|reflexivity]. }
    apply in_inv in Hz1 as [<-|?%in_nil]; tauto.
  Qed.

  Program Definition monotone_RA : RA :=
    {| RA_car := monotone;
       op := monotone_op;
       unit := monotone_unit;
       valid x := True |}.
  Next Obligation.
  Proof.
    apply class_of_inj.
    intros c.
    setoid_rewrite in_app_iff.
    split; (intros (?&?&?); eexists; split; [|eassumption]); tauto.
  Qed.
  Next Obligation.
  Proof.
    apply class_of_inj.
    intros c.
    setoid_rewrite in_app_iff.
    split.
    - intros (d & Hd1 & Hd2).
      destruct Hd1 as [Hd1|Hd1].
      + apply in_monotone_op in Hd1 as [(e & He1 & He2)|(e & He1 & He2)].
        * exists e; split; [|etransitivity]; eauto.
        * destruct (in_monotone_op_back1 _ _ z He1) as (f & Hf1 & Hf2).
          exists f; split; [auto; fail|].
          etransitivity; [eassumption|etransitivity; eauto].
      + destruct (in_monotone_op_back2 _ y _ Hd1) as (e & He1 & He2).
        exists e; split; [auto; fail|].
        etransitivity; eauto.
    - intros (d & Hd1 & Hd2).
      destruct Hd1 as [Hd1|Hd1].
      + destruct (in_monotone_op_back1 _ _ y Hd1) as (e & He1 & He2).
        exists e; split; [auto; fail|].
        etransitivity; eauto.
      + apply in_monotone_op in Hd1 as [(e & He1 & He2)|(e & He1 & He2)].
        * destruct (in_monotone_op_back2 _ x _ He1) as (f & Hf1 & Hf2).
          exists f; split; [auto; fail|].
          etransitivity; [eassumption|etransitivity; eauto].
        * exists e; split; [|etransitivity]; eauto.
  Qed.
  Next Obligation.
  Proof.
    apply (uniquely_represented _ _ _ (representative x) (representative x));
    [|apply representative_represented|reflexivity].
    apply (related_represented
             _ _ (representative (monotone_op monotone_unit x))).
    { apply representative_represented. }
    intros c; split.
    - intros (d & Hd1 & Hd2).
      apply in_monotone_op in Hd1 as
          [(e & He1%monotone_unit_empty & He2)|(e & He1 & He2)]; [tauto|].
      exists e; split; [|etransitivity]; eauto.
    - intros (d & Hd1 & Hd2).
      destruct (in_monotone_op_back2 _ monotone_unit _ Hd1) as (e & He1 & He2).
      exists e; split; [auto; fail|].
      etransitivity; eauto.
  Qed.
  Next Obligation.
  Proof.
    apply (uniquely_represented _ _ _ (representative x) (representative x));
    [|apply representative_represented|reflexivity].
    apply (related_represented
             _ _ (representative (monotone_op x monotone_unit))).
    { apply representative_represented. }
    intros c; split.
    - intros (d & Hd1 & Hd2).
      apply in_monotone_op in Hd1 as
          [(e & He1 & He2)|(e & He1%monotone_unit_empty & He2)]; [|tauto].
      exists e; split; [|etransitivity]; eauto.
    - intros (d & Hd1 & Hd2).
      destruct (in_monotone_op_back1 _ _ monotone_unit Hd1) as (e & He1 & He2).
      exists e; split; [auto; fail|].
      etransitivity; eauto.
  Qed.

  Lemma monotone_correct x y :
    po x y ↔ extension monotone_RA (principal x) (principal y).
  Proof.
    split.
    - intros Hxy.
      exists (principal y).
      apply class_of_inj.
      intros c; split.
      + intros (d & Hd1 & Hd2).
        apply is_in_monotone_preresntative_class_of in Hd1 as (e & He1 & He2).
        setoid_rewrite in_app_iff.
        exists e; split; [right|etransitivity]; eauto.
      + intros (d & Hd1 & Hd2).
        setoid_rewrite in_app_iff in Hd1.
        destruct Hd1 as [Hd1|Hd1].
        * apply in_principal in Hd1.
          exists y; split; [apply in_eq|].
          etransitivity; [eassumption| etransitivity]; eauto.
        * apply in_principal in Hd1.
          exists y; split; [apply in_eq|].
          etransitivity; eauto.
    - intros [a Ha].
      assert (monotone_rel
                (principal_base y)
                (monotone_base_op
                   (representative (principal x))
                   (representative a)))
        as Hrel by (apply equal_classes; trivial).
      pose proof (is_in_monotone_preresntative_class_of x (principal_base x))
        as (z & Hz1 & Hz2).
      { apply in_eq. }
      specialize (Hrel x) as [_ (w & Hw1 & Hw2)].
      { setoid_rewrite in_app_iff.
        exists z; split; [left; trivial|trivial]. }
      apply in_inv in Hw1 as [<-|?%in_nil]; tauto.
  Qed.

End monotone.

Program Definition monotone_RA_morph (po po' : PO) (f : PO_morphism po po') :
  RA_morphism (monotone_RA po) (monotone_RA po') :=
  {| RAM_mor x := class_of (monotone_rel po') (map f (representative x)) |}.
Next Obligation.
Proof.
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
  apply class_of_inj.
  intros x; split.
  - intros (d & Hd1 & Hd2).
    apply in_map_iff in Hd1 as [d' [<- Hd'%monotone_unit_empty]]; tauto.
  - intros (d & [] & Hd2).
Qed.

Local Obligation Tactic := idtac.

Program Definition monotone_RA_functor : Functor PO_cat RA_cat :=
  {| FO := monotone_RA;
     FA := monotone_RA_morph |}.
Next Obligation.
Proof.
  intros po.
  apply RAM_morphism_eq.
  intros a; cbn.
  rewrite map_id.
  apply class_of_representative.
Qed.
Next Obligation.
Proof.
  intros po po' po'' f g.
  apply RAM_morphism_eq.
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
