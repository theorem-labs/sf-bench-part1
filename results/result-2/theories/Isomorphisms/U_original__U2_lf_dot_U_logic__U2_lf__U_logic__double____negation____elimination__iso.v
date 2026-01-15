From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


Monomorphic Definition imported_Original_LF__DOT__Logic_LF_Logic_double__negation__elimination : SProp := Imported.Original_LF__DOT__Logic_LF_Logic_double__negation__elimination.

(* Helper functions to convert between False and MyFalse *)
Definition MyFalse_to_False (mf : Imported.MyFalse) : False := match mf with end.
Definition False_to_MyFalse (f : False) : Imported.MyFalse := match f with end.

(* Convert between Prop and SProp versions of double negation elimination *)
Definition dne_Prop_to_SProp : (forall P : Prop, ~ ~ P -> P) -> (forall P : SProp, Imported.Logic_not (Imported.Logic_not P) -> P) :=
  fun dne P nnp =>
    let P' := inhabited P in
    let nnP' : ~ ~ P' := fun np => MyFalse_to_False (nnp (fun p => False_to_MyFalse (np (inhabits p)))) in
    inhabitant (dne P' nnP').

Definition dne_SProp_to_Prop : (forall P : SProp, Imported.Logic_not (Imported.Logic_not P) -> P) -> (forall P : Prop, ~ ~ P -> P) :=
  fun dne P nnp =>
    let P' := SInhabited P in
    let nnP' : Imported.Logic_not (Imported.Logic_not P') := fun np => False_to_MyFalse (nnp (fun p => MyFalse_to_False (np (sinhabits p)))) in
    sinhabitant (dne P' nnP').

Monomorphic Instance Original_LF__DOT__Logic_LF_Logic_double__negation__elimination_iso : Iso Original.LF_DOT_Logic.LF.Logic.double_negation_elimination imported_Original_LF__DOT__Logic_LF_Logic_double__negation__elimination.
Proof.
  apply Build_Iso with (to := dne_Prop_to_SProp) (from := dne_SProp_to_Prop).
  - intro x.
    apply IsoEq.functional_extensionality_dep. intro P.
    apply IsoEq.functional_extensionality_dep. intro nnp.
    (* Both sides have type P : SProp, so definitionally equal *)
    reflexivity.
  - intro x.
    apply IsoEq.functional_extensionality_dep. intro P.
    apply IsoEq.functional_extensionality_dep. intro nnp.
    (* Both sides have type P : Prop, use proof irrelevance *)
    apply IsoEq.seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.double_negation_elimination := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_double__negation__elimination := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.double_negation_elimination Original_LF__DOT__Logic_LF_Logic_double__negation__elimination_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.double_negation_elimination Imported.Original_LF__DOT__Logic_LF_Logic_double__negation__elimination Original_LF__DOT__Logic_LF_Logic_double__negation__elimination_iso := {}.