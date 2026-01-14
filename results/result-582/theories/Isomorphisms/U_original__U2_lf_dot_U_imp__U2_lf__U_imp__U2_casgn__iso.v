From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__aexp__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Isomorphisms.U_string__string__iso.

Notation imported_Original_LF__DOT__Imp_LF_Imp_CAsgn := Imported.CAsgn.

Instance Original_LF__DOT__Imp_LF_Imp_CAsgn_iso : forall (x1 : String.string) (x2 : imported_String_string),
  rel_iso String_string_iso x1 x2 ->
  forall (x3 : Original.LF_DOT_Imp.LF.Imp.aexp) (x4 : imported_Original_LF__DOT__Imp_LF_Imp_aexp),
  rel_iso Original_LF__DOT__Imp_LF_Imp_aexp_iso x3 x4 -> rel_iso Original_LF__DOT__Imp_LF_Imp_com_iso (Original.LF_DOT_Imp.LF.Imp.CAsgn x1 x3) (imported_Original_LF__DOT__Imp_LF_Imp_CAsgn x2 x4).
Proof.
  intros x1 x2 H1 x3 x4 H2.
  unfold rel_iso in *.
  simpl.
  apply f_equal2; assumption.
Qed.

Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.CAsgn := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant imported_Original_LF__DOT__Imp_LF_Imp_CAsgn := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.CAsgn Original_LF__DOT__Imp_LF_Imp_CAsgn_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.CAsgn imported_Original_LF__DOT__Imp_LF_Imp_CAsgn Original_LF__DOT__Imp_LF_Imp_CAsgn_iso := {}.
