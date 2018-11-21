From iris.algebra Require Export cmra.
From iris.base_logic Require Import base_logic.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments op _ _ _ !_ /.
Local Arguments pcore _ _ !_ /.

(**

The idea is as follows: given a preorder relation R ⊆ A × A, we
construct a monoid (resource algebra) such that the extension order of
the monoid corresponds to the relation R. We do this by taking the
monoid to be the free join-semi-lattice completion of the relation
R. The monoid operation then is just join. The representative of an
element a ∈ A, is written as principal R a.

*)

Definition monotone {A : Type} (R : relation A) : Type := list A.

Definition principal {A : Type} (R : relation A) (a : A) :
  monotone R := [a].

Section monotone.
Local Set Default Proof Using "Type".
Context {A : ofeT} {R : relation A}.
Implicit Types a b : A.
Implicit Types x y : monotone R.

(* OFE *)
Instance monotone_dist : Dist (monotone R) :=
  λ n x y, ∀ a, (∃ b, b ∈ x ∧ R a b) ↔ (∃ b, b ∈ y ∧ R a b).

Instance monotone_equiv : Equiv (monotone R) := λ x y, ∀ n, x ≡{n}≡ y.

Definition monotone_ofe_mixin : OfeMixin (monotone R).
Proof.
  split.
  - rewrite /equiv /monotone_equiv /dist /monotone_dist; intuition auto using O.
  - intros n; split.
    + rewrite /dist /monotone_dist /equiv /monotone_equiv; intuition.
    + rewrite /dist /monotone_dist /equiv /monotone_equiv; intros ? ? Heq a.
      split; apply Heq.
    + rewrite /dist /monotone_dist /equiv /monotone_equiv;
        intros ? ? ? Heq Heq' a.
      split; intros Hxy.
      * apply Heq'; apply Heq; auto.
      * apply Heq; apply Heq'; auto.
  - intros n x y; rewrite /dist /monotone_dist; auto.
Qed.
Canonical Structure monotoneC := OfeT (monotone R) monotone_ofe_mixin.

(* CMRA *)
Instance monotone_validN : ValidN (monotone R) := λ n x, True.
Instance monotone_valid : Valid (monotone R) := λ x, True.

Program Instance monotone_op : Op (monotone R) := λ x y, x ++ y.
Instance monotone_pcore : PCore (monotone R) := Some.

Instance monotone_comm : Comm (≡) (@op (monotone R) _).
Proof. intros x y n a; setoid_rewrite elem_of_app; split=> Ha; firstorder. Qed.
Instance monotone_assoc : Assoc (≡) (@op (monotone R) _).
Proof.
  intros x y z n a; simpl; repeat setoid_rewrite elem_of_app; split=> Ha; firstorder.
Qed.
Lemma monotone_idemp (x : monotone R) : x ⋅ x ≡ x.
Proof. intros n a; setoid_rewrite elem_of_app; split=> Ha; firstorder. Qed.

Instance monotone_validN_ne n :
  Proper (dist n ==> impl) (@validN (monotone R) _ n).
Proof. intros x y ?; rewrite /impl; auto. Qed.
Instance monotone_validN_proper n : Proper (equiv ==> iff) (@validN (monotone R) _ n).
Proof. move=> x y /equiv_dist H; auto. Qed.

Instance monotone_op_ne' x : NonExpansive (op x).
Proof.
  intros n y1 y2; rewrite /dist /monotone_dist /equiv /monotone_equiv.
  rewrite /=; setoid_rewrite elem_of_app => Heq a.
  specialize (Heq a); destruct Heq as [Heq1 Heq2].
  split; intros [b [[Hb|Hb] HRb]]; eauto.
  - destruct Heq1 as [? [? ?]]; eauto.
  - destruct Heq2 as [? [? ?]]; eauto.
Qed.
Instance monotone_op_ne : NonExpansive2 (@op (monotone R) _).
Proof. by intros n x1 x2 Hx y1 y2 Hy; rewrite Hy !(comm _ _ y2) Hx. Qed.
Instance monotone_op_proper : Proper ((≡) ==> (≡) ==> (≡)) op := ne_proper_2 _.

Lemma monotone_included (x y : monotone R) : x ≼ y ↔ y ≡ x ⋅ y.
Proof.
  split; [|by intros ?; exists y].
  by intros [z Hz]; rewrite Hz assoc monotone_idemp.
Qed.

Definition monotone_cmra_mixin : CmraMixin (monotone R).
Proof.
  apply cmra_total_mixin; try apply _ || by eauto.
  - intros ?; apply monotone_idemp.
  - rewrite /equiv /monotone_equiv /dist /monotone_dist; eauto.
Qed.
Canonical Structure monotoneR : cmraT := CmraT (monotone R) monotone_cmra_mixin.

Global Instance monotone_cmra_total : CmraTotal monotoneR.
Proof. rewrite /CmraTotal; eauto. Qed.
Global Instance monotone_core_id (x : monotone R) : CoreId x.
Proof. by constructor. Qed.

Global Instance monotone_cmra_discrete : CmraDiscrete monotoneR.
Proof.
  split; auto;
    rewrite /OfeDiscrete /Discrete
            /equiv /ofe_equiv /= /cmra_equiv /= /monotone_equiv
            /dist /monotone_dist; eauto.
Qed.

Instance monotone_empty : Unit (monotone R) := @nil A.
Lemma auth_ucmra_mixin : UcmraMixin (monotone R).
Proof. split; done. Qed.

Canonical Structure monotoneUR := UcmraT (monotone R) auth_ucmra_mixin.

Global Instance principal_ne
       `{HRne : !∀ n, Proper ((dist n) ==> (dist n) ==> iff) R} :
  NonExpansive (principal R).
Proof.
  rewrite /principal /= => n a1 a2 Ha; split; simpl;
    setoid_rewrite elem_of_list_singleton; intros [x [Hx HR]]; subst;
    eexists; (split; first eauto).
  - symmetry in Ha. eapply HRne; eauto.
  - eapply HRne; eauto.
Qed.

Global Instance principal_proper
       {HRne : ∀ n, Proper ((dist n) ==> (dist n) ==> iff) R} :
  Proper ((≡) ==> (≡)) (principal R) := ne_proper _.

Global Instance principal_discrete a : Discrete (principal R a).
Proof.
  intros y; rewrite /dist /ofe_dist /= /equiv /ofe_equiv /= /monotone_equiv;
    eauto.
Qed.

Lemma principal_injN_general n a b :
  principal R a ≡{n}≡ principal R b → R a a → R a b.
Proof.
  rewrite /principal /dist /monotone_dist => Hab Haa.
  - destruct (Hab a) as [Ha _]; edestruct Ha as [? [?%elem_of_list_singleton ?]];
    subst; eauto.
    eexists _; split; first apply elem_of_list_singleton; eauto.
Qed.

Lemma principal_inj_general a b :
  principal R a ≡ principal R b → R a a → R a b.
Proof. intros Hab; apply (principal_injN_general 0); eauto. Qed.

Global Instance principal_injN_general' `{!Reflexive R} n :
  Inj (λ a b, R a b ∧ R b a) (dist n) (principal R).
Proof.
  intros x y Hxy; split; eapply (principal_injN_general n); eauto.
Qed.

Global Instance principal_inj_general' `{!Reflexive R} :
  Inj (λ a b, R a b ∧ R b a) (≡) (principal R).
Proof.
  intros x y Hxy; specialize (Hxy 0); eapply principal_injN_general'; eauto.
Qed.

Global Instance principal_injN `{!Reflexive R} {Has : AntiSymm (≡) R} n :
  Inj (dist n) (dist n) (principal R).
Proof.
  intros x y [Hxy Hyx]%principal_injN_general'.
  erewrite (@anti_symm _ _ _ Has); eauto.
Qed.
Global Instance principal_inj `{!Reflexive R} `{!AntiSymm (≡) R} :
  Inj (≡) (≡) (principal R).
Proof. intros ???. apply equiv_dist=>n. by apply principal_injN, equiv_dist. Qed.

Lemma principal_R_op `{!Transitive R} a b :
  R a b → principal R a ⋅ principal R b ≡ principal R b.
Proof.
  intros HR.
  rewrite /= /monotone_op /=.
  intros ? z; split; simpl; setoid_rewrite elem_of_list_singleton;
    setoid_rewrite elem_of_cons; setoid_rewrite elem_of_list_singleton;
      intros [? Hab']; try destruct Hab'; simplify_eq; eauto.
  intuition subst; eauto.
Qed.

Lemma principal_op_R a b x :
  R a a → principal R a ⋅ x ≡ principal R b → R a b.
Proof.
  intros Ha HR.
  rewrite /= /monotone_op /=.
  destruct (HR 0 a) as [[z [HR1%elem_of_list_singleton HR2]] _];
    last by subst; eauto.
  rewrite /op /monotone_op /principal /=.
  eexists _; split; eauto. rewrite elem_of_cons; eauto.
Qed.

Lemma principal_op_R' `{!Reflexive R} a b x :
  principal R a ⋅ x ≡ principal R b → R a b.
Proof. intros; eapply principal_op_R; eauto. Qed.

Lemma principal_included `{!PreOrder R} a b :
  principal R a ≼ principal R b ↔ R a b.
Proof.
  split.
  - intros [z Hz]; eapply principal_op_R'; rewrite Hz; eauto.
  - intros ?; exists (principal R b). rewrite principal_R_op; eauto.
Qed.

(** Internalized properties *)
Lemma monotone_equivI `{!(∀ n : nat, Proper (dist n ==> dist n ==> iff) R)}
      `{!Reflexive R} `{!AntiSymm (≡) R} {M} a b :
  principal R a ≡ principal R b ⊣⊢ (a ≡ b : uPred M).
Proof.
  uPred.unseal. do 2 split.
  - intros Hx. exact: principal_injN.
  - intros Hx. exact: principal_ne.
Qed.
End monotone.

Instance: Params (@principal) 1.
Arguments monotoneC {_} _.
Arguments monotoneR {_} _.
Arguments monotoneUR {_} _.


(** Having an instance of this class for a relation R allows almost
all lemmas provided in this module to be used. See type classes
required by some of preceding the lemmas and instances in the to see
how this works.

The only lemma that requires extra conditions on R is the injectivity
of principal which requires antisymmetry. *)
Class ProperPreOrder {A : Type} `{Dist A} (R : relation A) := {
  ProperPreOrder_preorder :> PreOrder R;
  ProperPreOrder_ne :> ∀ n, Proper ((dist n) ==> (dist n) ==> iff) R
}.
