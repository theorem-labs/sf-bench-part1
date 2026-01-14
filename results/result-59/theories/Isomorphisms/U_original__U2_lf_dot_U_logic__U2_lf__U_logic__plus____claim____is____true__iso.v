From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__plus____claim__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_plus__claim__is__true : imported_Original_LF__DOT__Logic_LF_Logic_plus__claim := Imported.Original_LF__DOT__Logic_LF_Logic_plus__claim__is__true.

Instance Original_LF__DOT__Logic_LF_Logic_plus__claim__is__true_iso : rel_iso Original_LF__DOT__Logic_LF_Logic_plus__claim_iso Original.LF_DOT_Logic.LF.Logic.plus_claim_is_true imported_Original_LF__DOT__Logic_LF_Logic_plus__claim__is__true.
Proof.
  (* rel_iso i x y = eq (i x) y, which is in SProp *)
  (* Since both values are in SProp (imported_Original_LF__DOT__Logic_LF_Logic_plus__claim), 
     they are equal by SProp's proof irrelevance *)
  unfold rel_iso.
  (* The isomorphism's 'to' function maps any proof to imported_plus_claim_true *)
  (* We need to show eq imported_plus_claim_true imported_Original_LF__DOT__Logic_LF_Logic_plus__claim__is__true *)
  (* Both are of type imported_Original_LF__DOT__Logic_LF_Logic_plus__claim which is SProp *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.plus_claim_is_true := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_plus__claim__is__true := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.plus_claim_is_true Original_LF__DOT__Logic_LF_Logic_plus__claim__is__true_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.plus_claim_is_true Imported.Original_LF__DOT__Logic_LF_Logic_plus__claim__is__true Original_LF__DOT__Logic_LF_Logic_plus__claim__is__true_iso := {}.