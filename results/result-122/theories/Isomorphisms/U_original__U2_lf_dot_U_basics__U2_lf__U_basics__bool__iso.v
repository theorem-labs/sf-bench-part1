From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__Basics_LF_Basics_bool : Type := Imported.Original_LF__DOT__Basics_LF_Basics_bool.
Definition Original_LF__DOT__Basics_LF_Basics_bool_iso : Iso Original.LF_DOT_Basics.LF.Basics.bool imported_Original_LF__DOT__Basics_LF_Basics_bool :=
  Build_Iso
    (fun x => match x with
              | Original.LF_DOT_Basics.LF.Basics.true => Imported.Original_LF__DOT__Basics_LF_Basics_bool_true
              | Original.LF_DOT_Basics.LF.Basics.false => Imported.Original_LF__DOT__Basics_LF_Basics_bool_false
              end)
    (fun y => match y with
              | Imported.Original_LF__DOT__Basics_LF_Basics_bool_true => Original.LF_DOT_Basics.LF.Basics.true
              | Imported.Original_LF__DOT__Basics_LF_Basics_bool_false => Original.LF_DOT_Basics.LF.Basics.false
              end)
    (fun x => match x return IsomorphismDefinitions.eq
                (match match x with
                       | Imported.Original_LF__DOT__Basics_LF_Basics_bool_true => Original.LF_DOT_Basics.LF.Basics.true
                       | Imported.Original_LF__DOT__Basics_LF_Basics_bool_false => Original.LF_DOT_Basics.LF.Basics.false
                       end with
                 | Original.LF_DOT_Basics.LF.Basics.true => Imported.Original_LF__DOT__Basics_LF_Basics_bool_true
                 | Original.LF_DOT_Basics.LF.Basics.false => Imported.Original_LF__DOT__Basics_LF_Basics_bool_false
                 end)
                x
              with
              | Imported.Original_LF__DOT__Basics_LF_Basics_bool_true => IsomorphismDefinitions.eq_refl
              | Imported.Original_LF__DOT__Basics_LF_Basics_bool_false => IsomorphismDefinitions.eq_refl
              end)
    (fun x => match x return IsomorphismDefinitions.eq
                (match match x with
                       | Original.LF_DOT_Basics.LF.Basics.true => Imported.Original_LF__DOT__Basics_LF_Basics_bool_true
                       | Original.LF_DOT_Basics.LF.Basics.false => Imported.Original_LF__DOT__Basics_LF_Basics_bool_false
                       end with
                 | Imported.Original_LF__DOT__Basics_LF_Basics_bool_true => Original.LF_DOT_Basics.LF.Basics.true
                 | Imported.Original_LF__DOT__Basics_LF_Basics_bool_false => Original.LF_DOT_Basics.LF.Basics.false
                 end)
                x
              with
              | Original.LF_DOT_Basics.LF.Basics.true => IsomorphismDefinitions.eq_refl
              | Original.LF_DOT_Basics.LF.Basics.false => IsomorphismDefinitions.eq_refl
              end).
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_bool := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.bool Original_LF__DOT__Basics_LF_Basics_bool_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.bool Imported.Original_LF__DOT__Basics_LF_Basics_bool Original_LF__DOT__Basics_LF_Basics_bool_iso := {}.