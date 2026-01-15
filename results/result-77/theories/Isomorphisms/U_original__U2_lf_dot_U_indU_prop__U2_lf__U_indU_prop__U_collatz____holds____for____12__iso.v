From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_indU_prop__U2_lf__U_indU_prop__U_collatz____holds____for__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12 : imported_Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for
    (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S (imported_S imported_0)))))))))))) := Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12.

(* Both Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for_12 and 
   Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12 are axioms.
   The isomorphism between them follows from the Collatz_holds_for_iso.
   Since we're dealing with SProp (proof irrelevance), any two inhabitants of an SProp are equal. *)
Instance Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12_iso : rel_iso (Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))))))))))
    Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for_12 imported_Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12.
Proof.
  unfold rel_iso.
  simpl.
  (* The goal is Iso (Collatz_holds_for 12) (imported_Collatz_holds_for (nat_to_imported 12)) 
     with the two axioms as inhabitants.
     We need to show that to (iso) original = imported.
     Since the target is SProp, any two inhabitants are equal. *)
  
  (* rel_iso for Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for_iso gives us
     Iso (Original.Collatz 12) (Imported.Collatz (nat_to_imported 12))
     We have Original.Collatz_holds_for_12 : Original.Collatz 12
     and imported_Collatz_holds_for_12 : Imported.Collatz (nat_to_imported 12)
     The goal is to show to (Original.Collatz_12) = imported_Collatz_12
     Since the RHS is SProp, this is trivially true. *)
  
  (* Use the fact that both live in SProp *)
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12.
  unfold imported_Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for.
  
  (* The Iso was built using iso_Prop_SProp. The target is SProp. *)
  (* For SProp, all proofs are equal, so we just need to provide the right structure *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for_12 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for_12 Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.Collatz_holds_for_12 Imported.Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12 Original_LF__DOT__IndProp_LF_IndProp_Collatz__holds__for__12_iso := {}.