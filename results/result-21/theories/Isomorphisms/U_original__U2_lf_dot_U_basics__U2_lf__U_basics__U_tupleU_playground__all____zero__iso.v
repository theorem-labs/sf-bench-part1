From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_tupleU_playground__nybble__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.

Monomorphic Definition imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero : imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble -> imported_Original_LF__DOT__Basics_LF_Basics_bool := Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero.
Monomorphic Instance Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.TuplePlayground.nybble) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble),
  rel_iso Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble_iso x1 x2 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.TuplePlayground.all_zero x1) (imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero x2).
Proof.
  intros x1 x2 H12.
  destruct H12 as [H12].
  apply IsoEq.eq_of_seq in H12.
  subst x2.
  destruct x1 as [b0 b1 b2 b3].
  destruct b0, b1, b2, b3; simpl;
  unfold imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero; simpl;
  constructor; apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.TuplePlayground.all_zero := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.TuplePlayground.all_zero Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.TuplePlayground.all_zero Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero_iso := {}.