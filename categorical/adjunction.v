From Coq.Unicode Require Import Utf8.
From Coq.Program Require Import Tactics.
From Categories.Essentials Require Import Facts_Tactics Quotient.
From Categories Require Import
     Essentials.Notations Category.Main Functor.Main Adjunction.Main
     NatTrans.Main.
From Coq.Lists Require Import List.
From cat_monotone Require Import RA PreOrder monotone.

Local Obligation Tactic := idtac.

Program Definition unit_morphism c : PO_morphism c (extension_PO (monotone_RA c)) :=
  {| POM_mor x := principal _ x |}.
Next Obligation.
Proof.
  intros po x y Hxy; cbn.
  apply monotone_correct; trivial.
Qed.

Program Definition unit_of_adjunction :
  ((Functor_id PO_cat) --> (extension_functor ∘ monotone_RA_functor))%nattrans :=
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

Program Definition co_uni_morphism c :
  RA_morphism (monotone_RA (extension_PO c)) c :=
{| RAM_mor x := fold_left (λ y z, op c y z) (representative x) (unit c) |}.
Next Obligation.
Proof.
  cbn.


Program Definition counit_of_adjunction :
  (monotone_RA_functor ∘ extension_functor --> Functor_id RA_cat)%nattrans :=
{| Trans := _ |}.
Next Obligation.
simpl.

Program Definition monote_left_adjoint_to_extension :
  (monotone_RA_functor ⊣_ucu extension_functor)%functor :=
  {| ucu_adj_unit := unit_of_adjunction |}.
Next Obligation.
Proof.

