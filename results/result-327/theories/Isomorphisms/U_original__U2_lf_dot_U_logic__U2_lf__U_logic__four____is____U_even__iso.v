From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_four__is__Even : imported_Original_LF__DOT__Logic_LF_Logic_Even (imported_S (imported_S (imported_S (imported_S imported_0)))) := Imported.Original_LF__DOT__Logic_LF_Logic_four__is__Even.

(* Since four_is_Even is Admitted in Original.v and declared as axiom in Lean,
   this isomorphism between two axioms can be proven using proof irrelevance *)
Instance Original_LF__DOT__Logic_LF_Logic_four__is__Even_iso : rel_iso (Original_LF__DOT__Logic_LF_Logic_Even_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original.LF_DOT_Logic.LF.Logic.four_is_Even imported_Original_LF__DOT__Logic_LF_Logic_four__is__Even.
Proof.
  unfold rel_iso.
  (* rel_iso for an Iso is: IsomorphismDefinitions.eq (to orig) imported *)
  (* Both are proofs in SProp, so they are equal by SProp proof irrelevance *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.four_is_Even := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_four__is__Even := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.four_is_Even Original_LF__DOT__Logic_LF_Logic_four__is__Even_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.four_is_Even Imported.Original_LF__DOT__Logic_LF_Logic_four__is__Even Original_LF__DOT__Logic_LF_Logic_four__is__Even_iso := {}.
