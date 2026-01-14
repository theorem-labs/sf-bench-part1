From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U_false__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_ex__falso__quodlibet : forall x : SProp, imported_Original_False -> x := Imported.Original_LF__DOT__Logic_LF_Logic_ex__falso__quodlibet.
Instance Original_LF__DOT__Logic_LF_Logic_ex__falso__quodlibet_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Original.False) (x4 : imported_Original_False),
  rel_iso
    {|
      to := Original_False_iso;
      from := from Original_False_iso;
      to_from := fun x : imported_Original_False => to_from Original_False_iso x;
      from_to := fun x : Original.False => seq_p_of_t (from_to Original_False_iso x)
    |} x3 x4 ->
  rel_iso hx (Original.LF_DOT_Logic.LF.Logic.ex_falso_quodlibet x1 x3) (imported_Original_LF__DOT__Logic_LF_Logic_ex__falso__quodlibet x2 x4).
Proof.
  intros x1 x2 hx x3 x4 Hrel.
  (* x3 is of type Original.False which is an empty type, so we can destruct it *)
  destruct x3.
Defined.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.ex_falso_quodlibet := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_ex__falso__quodlibet := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.ex_falso_quodlibet Original_LF__DOT__Logic_LF_Logic_ex__falso__quodlibet_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.ex_falso_quodlibet Imported.Original_LF__DOT__Logic_LF_Logic_ex__falso__quodlibet Original_LF__DOT__Logic_LF_Logic_ex__falso__quodlibet_iso := {}.