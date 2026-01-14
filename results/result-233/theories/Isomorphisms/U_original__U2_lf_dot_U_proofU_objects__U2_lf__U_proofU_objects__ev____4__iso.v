From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_proofU_objects__U2_lf__U_proofU_objects__ev__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__4 : imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev (imported_S (imported_S (imported_S (imported_S imported_0)))) := Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__4.

(* The rel_iso for ev_4 : we need to show that Original.ev_4 is related to imported_ev_4 via the ev isomorphism *)
(* The ev isomorphism at 4 is an Iso between (Original.ev 4) and (Imported.ev (nat_to_imported 4)) *)
(* rel_iso on an Iso means: to (iso) Original.ev_4 = imported_ev_4 *)
(* Since both types are SProps (ev in SProp), any two inhabitants are equal *)

Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__4_iso : rel_iso (Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso (S_iso (S_iso (S_iso (S_iso _0_iso))))) Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_4
    imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__4.
Proof.
  unfold rel_iso.
  (* The Iso between Original.ev 4 and Imported.ev (nat_to_imported 4) maps proofs via ev_to_imported *)
  (* Since Imported.ev ... is an SProp, any two elements are equal *)
  (* We need: to (Original_LF__DOT__ProofObjects_LF_ProofObjects_ev_iso ...) Original.ev_4 = imported_ev_4 *)
  (* Both are in SProp, so this is trivially true *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_4 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__4 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_4 Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__4_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.ev_4 Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__4 Original_LF__DOT__ProofObjects_LF_ProofObjects_ev__4_iso := {}.