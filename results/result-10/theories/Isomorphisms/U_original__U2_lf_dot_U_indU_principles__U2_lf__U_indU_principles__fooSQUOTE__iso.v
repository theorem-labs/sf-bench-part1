From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso.

Monomorphic Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo' : Type -> Type := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo'.

(* foo' is an inductive type with C1 and C2 constructors *)
(* The isomorphism is structural *)

Monomorphic Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo'_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.foo' x1) (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo' x2).
Proof.
  intros X1 X2 hx.
  pose (list_iso := @Original_LF__DOT__Poly_LF_Poly_list_iso X1 X2 hx).
  unshelve eapply Build_Iso.
  - (* to *)
    fix to_fn 1. intro f. destruct f as [l f'|].
    + exact (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo'_C1 X2 
              (to list_iso l) 
              (to_fn f')).
    + exact (Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo'_C2 X2).
  - (* from *)
    fix from_fn 1. intro f. destruct f as [l f'|].
    + exact (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.C1 X1
              (from list_iso l)
              (from_fn f')).
    + exact (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.C2 X1).
  - (* to_from *)
    fix IH 1. intro f. destruct f as [l f'|].
    + simpl. apply IsoEq.f_equal2.
      * exact (to_from list_iso l).
      * exact (IH f').
    + simpl. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    fix IH 1. intro f. destruct f as [l f'|].
    + simpl. apply seq_of_eq. f_equal.
      * pose proof (from_to list_iso l) as H.
        apply eq_of_seq in H. exact H.
      * apply eq_of_seq. exact (IH f').
    + simpl. apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.foo' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.foo' Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.foo' Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo' Original_LF__DOT__IndPrinciples_LF_IndPrinciples_foo'_iso := {}.