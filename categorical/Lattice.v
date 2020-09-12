From Coq.Unicode Require Import Utf8.
From Coq.Program Require Import Tactics.
From Categories.Essentials Require Import Facts_Tactics.
From Categories Require Import Category.Main Functor.Main.
From Coq.Classes Require Import RelationClasses.
From cat_monotone Require Import PartialOrder PCM.

(** We define join semi-lattices with a bottom element.  *)
Record JSLB := {
  JSLB_PO :> PO;
  join : JSLB_PO → JSLB_PO → JSLB_PO;
  bot : JSLB_PO;
  bot_least x : JSLB_PO bot x;
  join_UB1 x y : JSLB_PO x (join x y);
  join_UB2 x y : JSLB_PO y (join x y);
  join_LUB x y z : JSLB_PO x z → JSLB_PO y z → JSLB_PO (join x y) z;
}.

Lemma join_comm (c : JSLB) (x y : c) : join c x y = join c y x.
Proof.
  apply PO_antisymm.
  - apply join_LUB; [apply join_UB2|apply join_UB1].
  - apply join_LUB; [apply join_UB2|apply join_UB1].
Qed.

Lemma join_assoc (c : JSLB) (x y z : c) :
  join c (join c x y) z = join c x (join c y z).
Proof.
  apply PO_antisymm.
  - apply join_LUB.
    + apply join_LUB.
      * apply join_UB1.
      * etransitivity; [|apply join_UB2].
        apply join_UB1.
    + etransitivity; [|apply join_UB2].
      apply join_UB2.
  - apply join_LUB.
    + etransitivity; [|apply join_UB1].
      apply join_UB1.
    + apply join_LUB.
      * etransitivity; [|apply join_UB1].
        apply join_UB2.
      * apply join_UB2.
Qed.

Lemma join_bot (c : JSLB) (x : c) : join c x (bot c) = x.
Proof.
  apply PO_antisymm.
  - apply join_LUB; [reflexivity|].
    apply bot_least.
  - apply join_UB1.
Qed.

Record JSLB_morphism (j j' : JSLB) := {
  JSLBM_mor :> PO_morphism j j';
  JSLBM_resp x y : JSLBM_mor (join j x y) = join j' (JSLBM_mor x) (JSLBM_mor y);
  JSLBM_bot : JSLBM_mor (bot j) = bot j';
}.

Arguments JSLBM_mor {_ _} _.

Lemma JSLBM_morphism_eq (j j' : JSLB) (f g : JSLB_morphism j j') :
  (JSLBM_mor f = JSLBM_mor g) → f = g.
Proof.
  intros Hfg.
  destruct f as [f Hfresp Hfbot]; destruct g as [g Hgresp Hgbot];
    cbn in *; subst.
  PIR; trivial.
Qed.

Program Definition JSLB_id (j : JSLB) : JSLB_morphism j j :=
  {| JSLBM_mor := POM_id j |}.

Program Definition JSLB_comp (j j' j'' : JSLB)
  (f : JSLB_morphism j j') (g : JSLB_morphism j' j'') : JSLB_morphism j j'' :=
  {| JSLBM_mor := POM_comp _ _ _ (JSLBM_mor f) (JSLBM_mor g) |}.
Next Obligation.
Proof.
  repeat rewrite JSLBM_resp; trivial.
Qed.
Next Obligation.
Proof.
  repeat rewrite JSLBM_bot; trivial.
Qed.

Program Definition JSLB_cat : Category :=
  {| Obj := JSLB;
    Hom := JSLB_morphism;
    compose := JSLB_comp;
    id := JSLB_id |}.
Next Obligation.
Proof.
  apply JSLBM_morphism_eq, POM_morphism_eq; cbn; trivial.
Qed.
Next Obligation.
Proof.
  apply JSLBM_morphism_eq, POM_morphism_eq; cbn; trivial.
Qed.
Next Obligation.
Proof.
  apply JSLBM_morphism_eq, POM_morphism_eq; cbn; trivial.
Qed.
Next Obligation.
Proof.
  apply JSLBM_morphism_eq, POM_morphism_eq; cbn; trivial.
Qed.

Program Definition JSLB_forgetful_functor : Functor JSLB_cat PO_cat :=
  {| FO := JSLB_PO;
     FA := @JSLBM_mor; |}.

Program Definition RA_of_JSLB (j : JSLB) : PCM :=
{| PCM_car := PO_type j;
   op := join j;
   unit := bot j;
   valid x := True;
|}.
Next Obligation.
Proof.
  apply join_comm.
Qed.
Next Obligation.
Proof.
  apply join_assoc.
Qed.
Next Obligation.
Proof.
  rewrite join_comm. apply join_bot.
Qed.

