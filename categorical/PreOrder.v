From Coq.Unicode Require Import Utf8.
From Coq.Program Require Import Tactics.
From Categories.Essentials Require Import Facts_Tactics.
From Categories Require Import Category.Main.
From Coq.Classes Require Import RelationClasses.

Record PreOrd := {
  PRO_type :> Type;
  PRO_car :> PRO_type → PRO_type → Prop;
  PRO_PO : PreOrder PRO_car; }.

Existing Instance PRO_PO.

Record PRO_morphism (pro pro' : PreOrd) := {
  PROM_mor :> pro → pro';
  PROM_mono x y : pro x y → pro' (PROM_mor x) (PROM_mor y) }.

Arguments PROM_mor {_ _} _ _.

Lemma PROM_morphism_eq (pro pro' : PreOrd) (f g : PRO_morphism pro pro') :
  (∀ x, f x = g x) → f = g.
Proof.
  intros Hfg.
  assert (PROM_mor f = PROM_mor g) by (FunExt; auto).
  destruct f as [f Hfmono]; destruct g as [g Hgmono];
    cbn in *; subst.
  PIR; trivial.
Qed.

Program Definition POM_id (pro : PreOrd) : PRO_morphism pro pro :=
  {| PROM_mor x := x |}.

Program Definition PROM_comp (pro pro' pro'' : PreOrd)
  (f : PRO_morphism pro pro') (g : PRO_morphism pro' pro'')
  : PRO_morphism pro pro'' :=
  {| PROM_mor x := g (f x) |}.
Next Obligation.
Proof.
  repeat apply PROM_mono; trivial.
Qed.

Program Definition PreOrd_cat : Category :=
  {| Obj := PreOrd;
    Hom := PRO_morphism;
    compose := PROM_comp;
    id := POM_id |}.
Next Obligation.
Proof.
  apply PROM_morphism_eq; cbn; trivial.
Qed.
Next Obligation.
Proof.
  apply PROM_morphism_eq; cbn; trivial.
Qed.
Next Obligation.
Proof.
  apply PROM_morphism_eq; cbn; trivial.
Qed.
Next Obligation.
Proof.
  apply PROM_morphism_eq; cbn; trivial.
Qed.
