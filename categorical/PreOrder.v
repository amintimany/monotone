From Coq.Unicode Require Import Utf8.
From Coq.Program Require Import Tactics.
From Categories.Essentials Require Import Facts_Tactics.
From Categories Require Import Category.Main.
From Coq.Classes Require Import RelationClasses.

Record PO := {
  PO_type :> Type;
  PO_car :> PO_type → PO_type → Prop;
  PO_PO : PreOrder PO_car }.

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
