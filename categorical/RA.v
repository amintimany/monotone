From Coq.Unicode Require Import Utf8.
From Coq.Program Require Import Tactics.
From Categories.Essentials Require Import Facts_Tactics.
From Categories Require Import Category.Main Functor.Main.
From Coq.Classes Require Import RelationClasses.
From cat_monotone Require Import PartialOrder.

(** For us, an RA is basically a partial commutative monoid. *)
Record RA := {
  RA_car :> Type;
  op : RA_car → RA_car → RA_car;
  unit : RA_car;
  valid : RA_car → Prop;
  op_comm x y : op x y = op y x;
  op_assoc x y z : op (op x y) z = op x (op y z);
  unit_valid : valid unit;
  unit_id x : op unit x = x;
}.

Record RA_morphism (r r' : RA) := {
  RAM_mor :> r → r';
  RAM_valid x : valid r x → valid r' (RAM_mor x);
  RAM_resp x y : RAM_mor (op r x y) = op r' (RAM_mor x) (RAM_mor y);
  RAM_unit : RAM_mor (unit r) = unit r' }.

Arguments RAM_mor {_ _} _ _.

Lemma RAM_morphism_eq (r r' : RA) (f g : RA_morphism r r') :
  (∀ x, f x = g x) → f = g.
Proof.
  intros Hfg.
  assert (RAM_mor f = RAM_mor g) by (FunExt; auto).
  destruct f as [f Hfv Hfresp Hfunit]; destruct g as [g Hgv Hgresp Hgunit];
    cbn in *; subst.
  PIR; trivial.
Qed.

Program Definition RAM_id (r : RA) : RA_morphism r r :=
  {| RAM_mor x := x |}.

Program Definition RAM_comp (r r' r'' : RA)
        (f : RA_morphism r r') (g : RA_morphism r' r'') : RA_morphism r r'' :=
  {| RAM_mor x := g (f x) |}.
Next Obligation.
Proof.
  repeat apply RAM_valid; trivial.
Qed.
Next Obligation.
Proof.
  repeat rewrite RAM_resp; trivial.
Qed.
Next Obligation.
Proof.
  repeat rewrite RAM_unit; trivial.
Qed.

Program Definition RA_cat : Category :=
  {| Obj := RA;
    Hom := RA_morphism;
    compose := RAM_comp;
    id := RAM_id |}.
Next Obligation.
Proof.
  apply RAM_morphism_eq; cbn; trivial.
Qed.
Next Obligation.
Proof.
  apply RAM_morphism_eq; cbn; trivial.
Qed.
Next Obligation.
Proof.
  apply RAM_morphism_eq; cbn; trivial.
Qed.
Next Obligation.
Proof.
  apply RAM_morphism_eq; cbn; trivial.
Qed.

(** extension order forms a functor from RA_cat to PO_cat. *)

Definition extension (r : RA) (x y : r) : Prop := ∃ z, y = op r x z.

Program Definition extension_PreOrder (r : RA) : PreOrder (extension r).
Proof.
  split.
  - intros x; exists (unit r); rewrite op_comm, unit_id; trivial.
  - intros x y z [u Hu] [v Hv].
    exists (op r u v).
    rewrite Hv, Hu, op_assoc; trivial.
Qed.

Local Obligation Tactic := idtac.

(* Program Definition extension_Fun_mor (r r' : RA) (f : RA_morphism r r') : *)
(*   PO_morphism (extension_PO r) (extension_PO r') := *)
(*   {| POM_mor x := f x |}. *)
(* Next Obligation. *)
(* Proof. *)
(*   intros r r' f x y [z ->]; cbn. *)
(*   rewrite RAM_resp. *)
(*   exists (f z); trivial. *)
(* Qed. *)

(* Program Definition extension_functor : Functor RA_cat PO_cat := *)
(*   {| FO := extension_PO; *)
(*      FA := extension_Fun_mor |}. *)
(* Next Obligation. *)
(* Proof. *)
(*   intros r. *)
(*   apply POM_morphism_eq; cbn; trivial. *)
(* Qed. *)
(* Next Obligation. *)
(* Proof. *)
(*   intros r r' r'' f g. *)
(*   apply POM_morphism_eq; cbn; trivial. *)
(* Qed. *)
