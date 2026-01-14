From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_time : Type := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_time.

(* Define the forward and backward mappings *)
Definition time_to_imported (t : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.time) : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_time :=
  match t with
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.day => Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_time_day
  | Original.LF_DOT_IndPrinciples.LF.IndPrinciples.night => Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_time_night
  end.

Definition imported_to_time (t : imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_time) : Original.LF_DOT_IndPrinciples.LF.IndPrinciples.time :=
  match t with
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_time_day => Original.LF_DOT_IndPrinciples.LF.IndPrinciples.day
  | Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_time_night => Original.LF_DOT_IndPrinciples.LF.IndPrinciples.night
  end.

Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_time_iso : Iso Original.LF_DOT_IndPrinciples.LF.IndPrinciples.time imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_time.
Proof.
  apply (Build_Iso time_to_imported imported_to_time).
  - intro x. destruct x; apply IsomorphismDefinitions.eq_refl.
  - intro y. destruct y; apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.time := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_time := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.time Original_LF__DOT__IndPrinciples_LF_IndPrinciples_time_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.time Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_time Original_LF__DOT__IndPrinciples_LF_IndPrinciples_time_iso := {}.