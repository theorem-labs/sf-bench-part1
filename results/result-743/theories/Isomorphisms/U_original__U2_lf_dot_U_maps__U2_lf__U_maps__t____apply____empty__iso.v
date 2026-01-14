From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____empty__iso.

Definition imported_Original_LF__DOT__Maps_LF_Maps_t__apply__empty : forall (x : Type) (x0 : imported_String_string) (x1 : x), imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Maps_LF_Maps_t__empty x1 x0) x1 := Imported.Original_LF__DOT__Maps_LF_Maps_t__apply__empty.

(* This is an isomorphism between two axioms. Both sides are admitted lemmas:
   - Original.LF_DOT_Maps.LF.Maps.t_apply_empty is Admitted in Original.v
   - Imported.Original_LF__DOT__Maps_LF_Maps_t__apply__empty is an axiom from Lean
   Since these are both axioms stating the same thing (t_empty v x = v),
   and the isomorphism is between SProp terms (eq proofs), we can use proof
   irrelevance to show they are related. *)
Instance Original_LF__DOT__Maps_LF_Maps_t__apply__empty_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4) (x5 : x1) (x6 : x2) (hx1 : rel_iso hx x5 x6),
  rel_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Maps_LF_Maps_t__empty_iso hx1 hx0) hx1) (Original.LF_DOT_Maps.LF.Maps.t_apply_empty x1 x3 x5)
    (imported_Original_LF__DOT__Maps_LF_Maps_t__apply__empty x4 x6).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 hx1.
  (* rel_iso on an Iso between Prop and SProp types is just SProp equality *)
  (* Both sides are proofs of equality (one in Prop, one in SProp) *)
  (* We need to show these are related under the isomorphism *)
  unfold rel_iso. simpl.
  (* The goal is to show that the 'to' function of Corelib_Init_Logic_eq_iso 
     applied to t_apply_empty equals imported_Original_LF__DOT__Maps_LF_Maps_t__apply__empty *)
  (* Since the codomain is SProp, all inhabitants are equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Maps.LF.Maps.t_apply_empty := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Maps_LF_Maps_t__apply__empty := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Maps.LF.Maps.t_apply_empty Original_LF__DOT__Maps_LF_Maps_t__apply__empty_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Maps.LF.Maps.t_apply_empty Imported.Original_LF__DOT__Maps_LF_Maps_t__apply__empty Original_LF__DOT__Maps_LF_Maps_t__apply__empty_iso := {}.