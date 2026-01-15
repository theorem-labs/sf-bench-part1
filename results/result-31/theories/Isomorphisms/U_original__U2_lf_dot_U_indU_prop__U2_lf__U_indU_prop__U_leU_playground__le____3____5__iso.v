From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
From IsomorphismChecker Require Original Imported.
#[local] Set Printing Coercions.

From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_s__iso Isomorphisms.le__iso.

(* le_3_5 uses Imported.le which is the same as imported_le from le__iso *)
Monomorphic Definition imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5 : 
  imported_le (imported_S (imported_S (imported_S imported_0))) 
              (imported_S (imported_S (imported_S (imported_S (imported_S imported_0))))) 
  := Imported.Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5.

(* The isomorphism uses le_iso since Original.le_3_5 : Peano.le 3 5 and 
   Imported.le__3__5 : Imported.le 3 5 *)
(* Both le_3_5 are admitted/axiomatic, so we admit this isomorphism *)
Monomorphic Instance Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5_iso : 
  rel_iso (le_iso (S_iso (S_iso (S_iso _0_iso))) (S_iso (S_iso (S_iso (S_iso (S_iso _0_iso)))))) 
    Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le_3_5
    imported_Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5.
Proof.
  constructor. apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le_3_5 := {}. 
Instance: KnownConstant Imported.Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5 := {}. 
Instance: IsoStatementProofFor Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le_3_5 Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndProp.LF.IndProp.LePlayground.le_3_5 Imported.Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5 Original_LF__DOT__IndProp_LF_IndProp_LePlayground_le__3__5_iso := {}.
