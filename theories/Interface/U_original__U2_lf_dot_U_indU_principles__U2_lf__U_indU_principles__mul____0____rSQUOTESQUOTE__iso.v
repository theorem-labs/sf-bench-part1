From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__U_p____m0r__iso.

Module Export CodeBlocks.

  Export (hints) Interface.nat__iso Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__U_p____m0r__iso.

  Export Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__U_p____m0r__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_indU_principles__U2_lf__U_indU_principles__U_p____m0r__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r'' : forall x : imported_nat, imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r x.
Parameter Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r''_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso (Original_LF__DOT__IndPrinciples_LF_IndPrinciples_P__m0r_iso hx) (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.mul_0_r'' x1)
    (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r'' x2).
Existing Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r''_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.mul_0_r'' ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r''_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.mul_0_r'' imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r'' ?x) => unify x Original_LF__DOT__IndPrinciples_LF_IndPrinciples_mul__0__r''_iso; constructor : typeclass_instances.


End Interface.