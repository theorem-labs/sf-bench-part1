From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_none__iso Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__empty__iso.

Definition imported_Original_LF__DOT__Maps_LF_Maps_apply__empty : forall (x : Type) (x0 : imported_String_string), imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Maps_LF_Maps_empty x x0) (imported_None x) := Imported.Original_LF__DOT__Maps_LF_Maps_apply__empty.

(* This isomorphism relates two axioms: Original.LF_DOT_Maps.LF.Maps.apply_empty and Imported.Original_LF__DOT__Maps_LF_Maps_apply__empty.
   Both are axioms stating that empty x = None. The isomorphism is between the proof objects (which are in Prop/SProp).
   Since the Corelib_Init_Logic_eq_iso is an isomorphism between Prop and SProp equalities, and we are
   relating axiom proofs, this is allowed to be Admitted per the problem statement. *)
Instance Original_LF__DOT__Maps_LF_Maps_apply__empty_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4),
  rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Maps_LF_Maps_empty_iso hx hx0) (None_iso hx)) (Original.LF_DOT_Maps.LF.Maps.apply_empty x1 x3)
    (imported_Original_LF__DOT__Maps_LF_Maps_apply__empty x2 x4).
Proof.
  intros x1 x2 hx x3 x4 hx0.
  (* Both sides are proofs of equality statements. The isomorphism between them is in SProp,
     which means we just need to show they're related via the eq_iso. *)
  unfold rel_iso. simpl.
  (* The to_from direction: from (to p) = p, where p is in Prop
     The from_to direction: to (from q) = q, where q is in SProp
     Both equalities are in SProp, so by proof irrelevance they're trivially true. *)
  exact IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Maps.LF.Maps.apply_empty := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Maps_LF_Maps_apply__empty := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Maps.LF.Maps.apply_empty Original_LF__DOT__Maps_LF_Maps_apply__empty_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Maps.LF.Maps.apply_empty Imported.Original_LF__DOT__Maps_LF_Maps_apply__empty Original_LF__DOT__Maps_LF_Maps_apply__empty_iso := {}.