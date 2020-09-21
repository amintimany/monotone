From Coq.Unicode Require Import Utf8.
From Coq.Program Require Import Tactics.
From Categories.Essentials Require Import Notations Facts_Tactics Quotient.
From Coq.Logic Require Import PropExtensionality.
From Categories Require Import
     Category.Main Functor.Main Adjunction.Main NatTrans.Main.
From Coq.Classes Require Import RelationClasses.
From cat_monotone Require Import PreOrder.

Record PO := {
  PO_type :> Type;
  PO_car :> PO_type → PO_type → Prop;
  PO_PO : PreOrder PO_car;
  PO_antisymm : ∀ x y, PO_car x y → PO_car y x → x = y }.

Existing Instance PO_PO.

Record PO_morphism (po po' : PO) := {
  POM_mor :> po → po';
  POM_mono x y : po x y → po' (POM_mor x) (POM_mor y) }.

Arguments POM_mor {_ _} _ _.

Lemma POM_morphism_eq (po po' : PO) (f g : PO_morphism po po') :
  (∀ x, f x = g x) → f = g.
Proof.
  intros Hfg.
  assert (POM_mor f = POM_mor g) by (FunExt; auto).
  destruct f as [f Hfmono]; destruct g as [g Hgmono];
    cbn in *; subst.
  PIR; trivial.
Qed.

Program Definition POM_id (po : PO) : PO_morphism po po :=
  {| POM_mor x := x |}.

Program Definition POM_comp (po po' po'' : PO)
  (f : PO_morphism po po') (g : PO_morphism po' po'') : PO_morphism po po'' :=
  {| POM_mor x := g (f x) |}.
Next Obligation.
Proof.
  repeat apply POM_mono; trivial.
Qed.

Program Definition PO_cat : Category :=
  {| Obj := PO;
    Hom := PO_morphism;
    compose := POM_comp;
    id := POM_id |}.
Next Obligation.
Proof.
  apply POM_morphism_eq; cbn; trivial.
Qed.
Next Obligation.
Proof.
  apply POM_morphism_eq; cbn; trivial.
Qed.
Next Obligation.
Proof.
  apply POM_morphism_eq; cbn; trivial.
Qed.
Next Obligation.
Proof.
  apply POM_morphism_eq; cbn; trivial.
Qed.

(** partial order to preorder *)
Definition preorder_of_partial_order (po : PO) : PreOrd :=
{| PRO_type := po; PRO_car := po |}.

Program Definition preorder_of_partial_order_morphism (po po' : PO)
           (f : PO_morphism po po')
  : PRO_morphism (preorder_of_partial_order po) (preorder_of_partial_order po') :=
{| PROM_mor := f; PROM_mono := POM_mono _ _ f |}.

Program Definition preorder_of_partial_order_func : Functor PO_cat PreOrd_cat :=
{| FO := preorder_of_partial_order; FA := preorder_of_partial_order_morphism |}.

Next Obligation.
Proof. apply PROM_morphism_eq; simpl; trivial. Qed.

(** preorder to partial order *)

Definition antisymm_rel_base (pro : PreOrd) (x y : pro) : Prop :=
  pro x y ∧ pro y x.

Program Definition antisymm_rel (pro : PreOrd) : EquiRel pro :=
  {| EQR_rel := antisymm_rel_base pro |}.
Next Obligation.
Proof.
  unfold antisymm_rel_base.
  split.
  - intros ?; split; reflexivity.
  - intros ???; tauto.
  - intros ??? [? ?] [? ?]; split; etransitivity; eauto.
Qed.

Definition partial_order_of_preorder_relation
  (pro : PreOrd) (x y : quotient (antisymm_rel pro)) : Prop :=
  pro (representative x) (representative y).

Lemma partial_order_of_preorder_relation_refl pro x :
  partial_order_of_preorder_relation pro x x.
Proof. unfold partial_order_of_preorder_relation; reflexivity. Qed.

Lemma partial_order_of_preorder_relation_trans pro x y z :
  partial_order_of_preorder_relation pro x y →
  partial_order_of_preorder_relation pro y z →
  partial_order_of_preorder_relation pro x z.
Proof. unfold partial_order_of_preorder_relation; etransitivity; eauto. Qed.

Lemma partial_order_of_preorder_relation_antisymm pro x y :
  partial_order_of_preorder_relation pro x y →
  partial_order_of_preorder_relation pro y x →
  x = y.
Proof.
  unfold partial_order_of_preorder_relation.
  intros Hxy Hyx.
  apply (uniquely_represented _ _ _ (representative x) (representative y));
  [apply representative_represented; fail|
   apply representative_represented; fail|].
  split; trivial.
 Qed.

Instance: ∀ pro, PreOrder (partial_order_of_preorder_relation pro).
Proof.
  intros; split.
  - intros ?; apply partial_order_of_preorder_relation_refl.
  - intros ???; apply partial_order_of_preorder_relation_trans.
Qed.

Program Definition partial_order_of_preorder (pro : PreOrd) : PO :=
{| PO_type := quotient (antisymm_rel pro);
   PO_car := partial_order_of_preorder_relation pro;
   PO_antisymm := partial_order_of_preorder_relation_antisymm pro|}.

Local Obligation Tactic := idtac.

Program Definition partial_order_of_preorder_morphism (pro pro' : PreOrd)
           (f : PRO_morphism pro pro')
  : PO_morphism (partial_order_of_preorder pro) (partial_order_of_preorder pro')
  := {| POM_mor := λ x, class_of (antisymm_rel pro') (f (representative x))|}.

Next Obligation.
Proof.
  intros pro pro' f x y Hxy; simpl in *.
  unfold partial_order_of_preorder_relation in *.
  etransitivity;
    [apply (representative_of_class_of
              (antisymm_rel pro') (f (representative x)))|].
  etransitivity;
    [|apply (representative_of_class_of
              (antisymm_rel pro') (f (representative y)))].
  apply (PROM_mono _ _ f); trivial.
Qed.

Program Definition partial_order_of_preorder_func : Functor PreOrd_cat PO_cat :=
{| FO := partial_order_of_preorder; FA := partial_order_of_preorder_morphism |}.

Next Obligation.
Proof.
  intros x.
  apply POM_morphism_eq; simpl; intros ?.
  apply class_of_representative.
Qed.
Next Obligation.
Proof.
  intros pro pro' por'' f g.
  apply POM_morphism_eq; simpl; intros ?.
  apply class_of_inj; split.
  - apply (PROM_mono _ _ g).
    etransitivity;
      [|apply (representative_of_class_of
                 (antisymm_rel pro') (f (representative x)))].
    reflexivity.
  - apply (PROM_mono _ _ g).
    etransitivity;
      [apply (representative_of_class_of
                 (antisymm_rel pro') (f (representative x)))|].
    reflexivity.
Qed.

(** properties of inclusion functor and back *)

Lemma preorder_of_partial_order_func_full :
  Full_Func preorder_of_partial_order_func.
Proof.
  intros po po' f; simpl in *.
  exists ({| POM_mor := f; POM_mono := (PROM_mono _ _ f) |}).
  apply PROM_morphism_eq; trivial.
Qed.

Lemma preorder_of_partial_order_func_faithful :
  Faithful_Func preorder_of_partial_order_func.
Proof.
  intros po po' f g Hfg; simpl in *.
  apply POM_morphism_eq.
  intros x.
  apply (equal_f (f_equal PROM_mor Hfg) x).
Qed.

Program Definition preorder_partial_order_adj_unit_map (pro : PreOrd) :
  PRO_morphism pro (preorder_of_partial_order (partial_order_of_preorder pro)) :=
{| PROM_mor := λ x, class_of (antisymm_rel pro) x  |}.

Next Obligation.
Proof.
  intros pro x y Hxy; simpl.
  unfold partial_order_of_preorder_relation.
  etransitivity;
      [apply (representative_of_class_of (antisymm_rel pro) x)|].
  etransitivity;
    [|apply (representative_of_class_of (antisymm_rel pro) y)].
  trivial.
Qed.

Program Definition preorder_partial_order_adj_unit :
  NatTrans (Functor_id PreOrd_cat)
           (preorder_of_partial_order_func ∘ partial_order_of_preorder_func) :=
{| Trans := preorder_partial_order_adj_unit_map |}.

Next Obligation.
Proof.
  intros pro pro' f; simpl in *.
  apply PROM_morphism_eq; intros x; simpl.
  apply class_of_inj; split; apply (PROM_mono _ _ f).
  - etransitivity;
    [|apply (representative_of_class_of (antisymm_rel pro) x)]; reflexivity.
  - etransitivity;
    [apply (representative_of_class_of (antisymm_rel pro) x)|]; reflexivity.
Qed.

Next Obligation.
Proof.
  intros pro pro' f; simpl in *.
  apply PROM_morphism_eq; intros x; simpl.
  apply class_of_inj; split; apply (PROM_mono _ _ f).
  - etransitivity;
    [|apply (representative_of_class_of (antisymm_rel pro) x)]; reflexivity.
  - etransitivity;
    [apply (representative_of_class_of (antisymm_rel pro) x)|]; reflexivity.
Qed.

Program Definition preorder_partial_order_adj_morph_ex (pro : PreOrd) (po : PO)
        ( f : PRO_morphism pro (preorder_of_partial_order po)) :
  PO_morphism (partial_order_of_preorder pro) po :=
{| POM_mor := λ x, f (representative x) |}.

Next Obligation.
Proof.
  intros pro po f x y Hxy; simpl in *.
  apply (PROM_mono _ _ f); trivial.
Qed.

Program Definition preorder_partial_order_adj :
  (partial_order_of_preorder_func ⊣ preorder_of_partial_order_func)%functor :=
{| adj_unit := preorder_partial_order_adj_unit;
   adj_morph_ex := preorder_partial_order_adj_morph_ex |}.

Next Obligation.
Proof.
  intros pro po f; simpl in *.
  apply PROM_morphism_eq; simpl in *.
  intros x.
  apply PO_antisymm.
  - apply (PROM_mono _ _ f).
    etransitivity;
    [|apply (representative_of_class_of (antisymm_rel pro) x)]; reflexivity.
  - apply (PROM_mono _ _ f).
    etransitivity;
    [apply (representative_of_class_of (antisymm_rel pro) x)|]; reflexivity.
Qed.
Next Obligation.
Proof.
  intros pro po f g h Hfg Hfh; simpl in *.
  pose proof (equal_f (f_equal PROM_mor Hfg)) as Hfg'; simpl in *.
  pose proof (equal_f (f_equal PROM_mor Hfh)) as Hfh'; simpl in *.
  apply POM_morphism_eq; intros x; simpl in *.
  specialize (Hfg' (representative x)).
  specialize (Hfh' (representative x)).
  rewrite class_of_representative in Hfg', Hfh'.
  rewrite <- Hfg', <- Hfh'; trivial.
Qed.
