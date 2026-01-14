From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_ascii__ascii__iso Isomorphisms.U_string__string__iso.

Definition imported_String_String : imported_Ascii_ascii -> imported_String_string -> imported_String_string := Imported.String_String.
Instance String_String_iso : forall (x1 : Ascii.ascii) (x2 : imported_Ascii_ascii),
  rel_iso Ascii_ascii_iso x1 x2 ->
  forall (x3 : String.string) (x4 : imported_String_string), rel_iso String_string_iso x3 x4 -> rel_iso String_string_iso (String.String x1 x3) (imported_String_String x2 x4).
Proof.
  intros x1 x2 H1 x3 x4 H3.
  unfold rel_iso in *. simpl in *.
  pose proof (eq_of_seq H1) as E1.
  pose proof (eq_of_seq H3) as E3.
  subst.
  unfold imported_String_String, Imported.String_String.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant String.String := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.String_String := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor String.String String_String_iso := {}.
Instance: IsoStatementProofBetween String.String Imported.String_String String_String_iso := {}.