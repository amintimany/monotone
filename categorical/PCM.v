From Coq.Unicode Require Import Utf8.
From Coq.Program Require Import Tactics.
From Categories.Essentials Require Import Facts_Tactics.
From Categories Require Import Category.Main Functor.Main.
From Coq.Classes Require Import RelationClasses.
From cat_monotone Require Import PartialOrder PreOrder.

(** For us, an RA is basically a partial commutative monoid. *)
Record PCM := {
  PCM_car :> Type;
  op : PCM_car → PCM_car → PCM_car;
  unit : PCM_car;
  valid : PCM_car → Prop;
  op_comm x y : op x y = op y x;
  op_assoc x y z : op (op x y) z = op x (op y z);
  unit_valid : valid unit;
  unit_id x : op unit x = x;
  valid_op x y : valid (op x y) → valid x
}.

Record PCM_morphism (r r' : PCM) := {
  PCMM_mor :> r → r';
  PCMM_valid x : valid r x → valid r' (PCMM_mor x);
  PCMM_resp x y : PCMM_mor (op r x y) = op r' (PCMM_mor x) (PCMM_mor y);
  PCMM_unit : PCMM_mor (unit r) = unit r' }.

Arguments PCMM_mor {_ _} _ _.

Lemma PCMM_morphism_eq (r r' : PCM) (f g : PCM_morphism r r') :
  (∀ x, f x = g x) → f = g.
Proof.
  intros Hfg.
  assert (PCMM_mor f = PCMM_mor g) by (FunExt; auto).
  destruct f as [f Hfv Hfresp Hfunit]; destruct g as [g Hgv Hgresp Hgunit];
    cbn in *; subst.
  PIR; trivial.
Qed.

Program Definition PCMM_id (r : PCM) : PCM_morphism r r :=
  {| PCMM_mor x := x |}.

Program Definition PCMM_comp (r r' r'' : PCM)
        (f : PCM_morphism r r') (g : PCM_morphism r' r'') : PCM_morphism r r'' :=
  {| PCMM_mor x := g (f x) |}.
Next Obligation.
Proof.
  repeat apply PCMM_valid; trivial.
Qed.
Next Obligation.
Proof.
  repeat rewrite PCMM_resp; trivial.
Qed.
Next Obligation.
Proof.
  repeat rewrite PCMM_unit; trivial.
Qed.

Program Definition PCM_cat : Category :=
  {| Obj := PCM;
    Hom := PCM_morphism;
    compose := PCMM_comp;
    id := PCMM_id |}.
Next Obligation.
Proof.
  apply PCMM_morphism_eq; cbn; trivial.
Qed.
Next Obligation.
Proof.
  apply PCMM_morphism_eq; cbn; trivial.
Qed.
Next Obligation.
Proof.
  apply PCMM_morphism_eq; cbn; trivial.
Qed.
Next Obligation.
Proof.
  apply PCMM_morphism_eq; cbn; trivial.
Qed.

(** extension order forms a functor from RA_cat to PO_cat. *)

Definition extension (r : PCM) (x y : r) : Prop := ∃ z, y = op r x z.

Instance extension_PreOrder (r : PCM) : PreOrder (extension r).
Proof.
  split.
  - intros x; exists (unit r); rewrite op_comm, unit_id; trivial.
  - intros x y z [u Hu] [v Hv].
    exists (op r u v).
    rewrite Hv, Hu, op_assoc; trivial.
Qed.

Program Definition extension_pro (r : PCM) : PreOrd :=
  {| PRO_type := r; PRO_car := extension r |}.

Local Obligation Tactic := idtac.

Program Definition extension_Fun_mor (r r' : PCM) (f : PCM_morphism r r') :
  PRO_morphism (extension_pro r) (extension_pro r') :=
  {| PROM_mor x := f x |}.
Next Obligation.
Proof.
  intros r r' f x y [z ->]; cbn.
  rewrite PCMM_resp.
  exists (f z); trivial.
Qed.

Program Definition extension_functor : Functor PCM_cat PreOrd_cat :=
  {| FO := extension_pro;
     FA := extension_Fun_mor |}.
Next Obligation.
Proof.
  intros r.
  apply PROM_morphism_eq; cbn; trivial.
Qed.
Next Obligation.
Proof.
  intros r r' r'' f g.
  apply PROM_morphism_eq; cbn; trivial.
Qed.
