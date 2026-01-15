From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib.Logic Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
#[local] Set Printing Coercions.


(* peirce is a Definition: forall P Q : Prop, ((P -> Q) -> P) -> P, which is a Prop *)
(* In SProp land, this becomes an SProp *)
Definition imported_Original_LF__DOT__Logic_LF_Logic_peirce : SProp := Imported.Original_LF__DOT__Logic_LF_Logic_peirce.

(* Build the isomorphism between peirce (Prop version) and imported (SProp version) *)
(* Key insight: Prop ≅ SProp via iso_Prop_SProp where to = SInhabited, from = inhabited *)

(* Helper: convert peirce from Prop to SProp version *)
Definition peirce_to : (forall P Q : Prop, ((P -> Q) -> P) -> P) -> 
                       (forall P Q : SProp, ((P -> Q) -> P) -> P).
Proof.
  intros H S T g.
  (* H : forall P Q : Prop, ((P->Q)->P)->P *)
  (* S, T : SProp *)
  (* g : (S -> T) -> S *)
  (* Goal: S *)
  specialize (H (inhabited S) (inhabited T)).
  (* H : ((inhabited S -> inhabited T) -> inhabited S) -> inhabited S *)
  assert (g' : (inhabited S -> inhabited T) -> inhabited S).
  { intro h.
    constructor.
    apply g.
    intro s.
    destruct (h (inhabits s)).
    assumption.
  }
  destruct (H g').
  assumption.
Defined.

(* Helper: convert peirce from SProp to Prop version *)
Definition peirce_from : (forall P Q : SProp, ((P -> Q) -> P) -> P) -> 
                         (forall P Q : Prop, ((P -> Q) -> P) -> P).
Proof.
  intros H P Q g.
  (* H : forall S T : SProp, ((S->T)->S)->S *)
  (* P, Q : Prop *)
  (* g : (P -> Q) -> P *)
  (* Goal: P *)
  specialize (H (SInhabited P) (SInhabited Q)).
  (* H : ((SInhabited P -> SInhabited Q) -> SInhabited P) -> SInhabited P *)
  assert (g' : (SInhabited P -> SInhabited Q) -> SInhabited P).
  { intro h.
    constructor.
    apply g.
    intro p.
    apply sinhabitant.
    apply h.
    constructor. exact p.
  }
  apply sinhabitant.
  exact (H g').
Defined.

(* peirce is not Admitted, just a definition. The types differ in Prop vs SProp *)
Instance Original_LF__DOT__Logic_LF_Logic_peirce_iso : Iso Original.LF_DOT_Logic.LF.Logic.peirce imported_Original_LF__DOT__Logic_LF_Logic_peirce.
Proof.
  unfold Original.LF_DOT_Logic.LF.Logic.peirce, imported_Original_LF__DOT__Logic_LF_Logic_peirce.
  unfold Imported.Original_LF__DOT__Logic_LF_Logic_peirce.
  apply Build_Iso with (to := peirce_to) (from := peirce_from).
  - (* to_from: peirce_to (peirce_from x) = x for x : SProp version *)
    intro x. 
    apply functional_extensionality_dep. intro P.
    apply functional_extensionality_dep. intro Q.
    apply functional_extensionality_dep. intro f.
    reflexivity. (* SProp proof irrelevance *)
  - (* from_to: peirce_from (peirce_to x) = x for x : Prop version *)
    intro x.
    apply functional_extensionality_dep. intro P.
    apply functional_extensionality_dep. intro Q.
    apply functional_extensionality_dep. intro f.
    apply seq_of_eq.
    apply proof_irrelevance.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.peirce := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_peirce := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.peirce Original_LF__DOT__Logic_LF_Logic_peirce_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.peirce Imported.Original_LF__DOT__Logic_LF_Logic_peirce Original_LF__DOT__Logic_LF_Logic_peirce_iso := {}.