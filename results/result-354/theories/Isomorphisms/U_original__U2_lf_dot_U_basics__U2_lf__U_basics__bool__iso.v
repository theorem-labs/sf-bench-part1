From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__Basics_LF_Basics_bool : Type := Imported.Original_LF__DOT__Basics_LF_Basics_bool.
Definition Original_LF__DOT__Basics_LF_Basics_bool_true := Imported.Original_LF__DOT__Basics_LF_Basics_bool_true.
Definition Original_LF__DOT__Basics_LF_Basics_bool_false := Imported.Original_LF__DOT__Basics_LF_Basics_bool_false.

Instance Original_LF__DOT__Basics_LF_Basics_bool_iso : Iso Original.LF_DOT_Basics.LF.Basics.bool imported_Original_LF__DOT__Basics_LF_Basics_bool.
Proof.
  unshelve eapply Build_Iso.
  - (* to *)
    exact (fun b => match b with
      | Original.LF_DOT_Basics.LF.Basics.true => Original_LF__DOT__Basics_LF_Basics_bool_true
      | Original.LF_DOT_Basics.LF.Basics.false => Original_LF__DOT__Basics_LF_Basics_bool_false
      end).
  - (* from *)
    exact (fun b => match b with
      | Imported.Original_LF__DOT__Basics_LF_Basics_bool_true => Original.LF_DOT_Basics.LF.Basics.true
      | Imported.Original_LF__DOT__Basics_LF_Basics_bool_false => Original.LF_DOT_Basics.LF.Basics.false
      end).
  - (* to_from *)
    intro b. destruct b; apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro b. destruct b; apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant imported_Original_LF__DOT__Basics_LF_Basics_bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.bool Original_LF__DOT__Basics_LF_Basics_bool_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.bool imported_Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_bool_iso := {}.