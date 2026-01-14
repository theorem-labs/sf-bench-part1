From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_otherNat : Type := Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_otherNat.

(* Define the forward function: Original -> Imported *)
Fixpoint orig_to_imported (x : Original.LF_DOT_Basics.LF.Basics.NatPlayground.otherNat) 
  : Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_otherNat :=
  match x with
  | Original.LF_DOT_Basics.LF.Basics.NatPlayground.stop => 
      Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_otherNat_stop
  | Original.LF_DOT_Basics.LF.Basics.NatPlayground.tick foo => 
      Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_otherNat_tick (orig_to_imported foo)
  end.

(* Define the backward function: Imported -> Original *)
Fixpoint imported_to_orig (x : Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_otherNat) 
  : Original.LF_DOT_Basics.LF.Basics.NatPlayground.otherNat :=
  match x with
  | Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_otherNat_stop => 
      Original.LF_DOT_Basics.LF.Basics.NatPlayground.stop
  | Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_otherNat_tick foo => 
      Original.LF_DOT_Basics.LF.Basics.NatPlayground.tick (imported_to_orig foo)
  end.

(* Prove round-trip properties using SProp equality *)
Lemma orig_imported_orig : forall x, IsomorphismDefinitions.eq (imported_to_orig (orig_to_imported x)) x.
Proof.
  fix IH 1.
  intro x.
  destruct x.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. apply IH.
Qed.

Lemma imported_orig_imported : forall x, IsomorphismDefinitions.eq (orig_to_imported (imported_to_orig x)) x.
Proof.
  fix IH 1.
  intro x.
  destruct x.
  - apply IsomorphismDefinitions.eq_refl.
  - simpl. apply IsoEq.f_equal. apply IH.
Qed.

Instance Original_LF__DOT__Basics_LF_Basics_NatPlayground_otherNat_iso : Iso Original.LF_DOT_Basics.LF.Basics.NatPlayground.otherNat imported_Original_LF__DOT__Basics_LF_Basics_NatPlayground_otherNat.
Proof.
  apply (Build_Iso orig_to_imported imported_to_orig).
  - apply imported_orig_imported.  (* to_from: orig_to_imported (imported_to_orig x) = x *)
  - apply orig_imported_orig.  (* from_to: imported_to_orig (orig_to_imported x) = x *)
Defined.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.NatPlayground.otherNat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_otherNat := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.NatPlayground.otherNat Original_LF__DOT__Basics_LF_Basics_NatPlayground_otherNat_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.NatPlayground.otherNat Imported.Original_LF__DOT__Basics_LF_Basics_NatPlayground_otherNat Original_LF__DOT__Basics_LF_Basics_NatPlayground_otherNat_iso := {}.