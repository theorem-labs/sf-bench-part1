From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


From IsomorphismChecker Require Export Isomorphisms.and__iso.

(* and_comm'_aux swaps the components of a conjunction.
   Since and_comm'_aux : P /\ Q -> Q /\ P, the imported version should be 
   imported_and x x0 -> imported_and x0 x, using the same and_iso as for Coq's and. *)

(* Define imported function using the and structure *)
(* and has constructor and_intro and projections left and right *)
Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE__aux : forall x x0 : SProp, imported_and x x0 -> imported_and x0 x :=
  fun x x0 H => @Imported.and_intro x0 x (Imported.right _ _ H) (Imported.left _ _ H).

Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE__aux_iso : forall (x1 : Prop) (x2 : SProp) (hx : Iso x1 x2) (x3 : Prop) (x4 : SProp) (hx0 : Iso x3 x4) (x5 : x1 /\ x3) (x6 : imported_and x2 x4),
  rel_iso (and_iso hx hx0) x5 x6 ->
  rel_iso (and_iso hx0 hx) (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.and_comm'_aux x1 x3 x5) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE__aux x6).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 H56.
  constructor. simpl.
  destruct x5 as [a b].
  destruct H56 as [H56']. simpl in H56'.
  destruct H56'.
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.and_comm'_aux := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE__aux := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.and_comm'_aux Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE__aux_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.and_comm'_aux imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE__aux Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE__aux_iso := {}.

(* Aliases for checker compatibility *)
Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'__aux := imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE__aux.
Definition Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__comm'__aux_iso := Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_and__commSQUOTE__aux_iso.