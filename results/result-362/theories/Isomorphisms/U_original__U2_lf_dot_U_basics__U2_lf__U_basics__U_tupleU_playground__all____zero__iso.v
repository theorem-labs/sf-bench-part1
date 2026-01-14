From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__U_tupleU_playground__nybble__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__bool__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero : imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble -> imported_Original_LF__DOT__Basics_LF_Basics_bool := Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero.

Instance Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.TuplePlayground.nybble) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble),
  rel_iso Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble_iso x1 x2 ->
  rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso (Original.LF_DOT_Basics.LF.Basics.TuplePlayground.all_zero x1) (imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero x2).
Proof.
  intros x1 x2 Hiso.
  (* x2 = to x1 from the isomorphism *)
  unfold rel_iso in Hiso.
  unfold Original_LF__DOT__Basics_LF_Basics_TuplePlayground_nybble_iso in Hiso.
  simpl in Hiso.
  (* Now Hiso says: nybble_to_imported x1 = x2 (in SProp eq) *)
  destruct x1 as [b0 b1 b2 b3].
  unfold imported_Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero.
  unfold rel_iso, Original_LF__DOT__Basics_LF_Basics_bool_iso. simpl.
  (* We need to show bool_to_imported (all_zero (bits b0 b1 b2 b3)) = all__zero x2 *)
  unfold nybble_to_imported in Hiso.
  (* Use the SProp eq to get a Leibniz eq *)
  destruct Hiso.
  (* Now we can compute both sides *)
  destruct b0, b1, b2, b3; apply IsomorphismDefinitions.eq_refl.
Qed.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.TuplePlayground.all_zero := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.TuplePlayground.all_zero Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.TuplePlayground.all_zero Imported.Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero Original_LF__DOT__Basics_LF_Basics_TuplePlayground_all__zero_iso := {}.