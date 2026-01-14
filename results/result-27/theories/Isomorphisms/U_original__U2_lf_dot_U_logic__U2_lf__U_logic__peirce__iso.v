From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


Definition imported_Original_LF__DOT__Logic_LF_Logic_peirce : SProp := Imported.Original_LF__DOT__Logic_LF_Logic_peirce.

(* Original: forall P Q : Prop, ((P -> Q) -> P) -> P  : Prop *)
(* Imported: forall P Q : SProp, ((P -> Q) -> P) -> P : SProp *)

(* Both are equivalent logical principles. We can convert between them using
   inhabited/SInhabited to bridge Prop and SProp *)

Definition peirce_Prop_to_SProp : 
  (forall P Q : Prop, ((P -> Q) -> P) -> P) -> 
  (forall P Q : SProp, ((P -> Q) -> P) -> P).
Proof.
  intro H.
  intros P Q HPQ.
  (* We need to produce P : SProp from H : forall P Q : Prop, ((P -> Q) -> P) -> P *)
  (* inhabited P : Prop, inhabited Q : Prop *)
  (* Use inhabited to convert SProp to Prop, then apply H *)
  pose proof (H (inhabited P) (inhabited Q)) as Hinstance.
  (* Hinstance : ((inhabited P -> inhabited Q) -> inhabited P) -> inhabited P *)
  assert (Hprem : (inhabited P -> inhabited Q) -> inhabited P).
  { intro HPQ'.
    apply inhabits.
    apply HPQ.
    intro HP.
    destruct (HPQ' (inhabits HP)) as [HQ].
    exact HQ. }
  destruct (Hinstance Hprem) as [HP].
  exact HP.
Defined.

Definition peirce_SProp_to_Prop :
  (forall P Q : SProp, ((P -> Q) -> P) -> P) ->
  (forall P Q : Prop, ((P -> Q) -> P) -> P).
Proof.
  intro H.
  intros P Q HPQ.
  (* H : forall P Q : SProp, ((P -> Q) -> P) -> P *)
  (* SInhabited P : SProp, SInhabited Q : SProp *)
  pose proof (H (SInhabited P) (SInhabited Q)) as Hinstance.
  (* Hinstance : ((SInhabited P -> SInhabited Q) -> SInhabited P) -> SInhabited P *)
  assert (Hprem : (SInhabited P -> SInhabited Q) -> SInhabited P).
  { intro HPQ'.
    apply sinhabits.
    apply HPQ.
    intro HP.
    apply sinhabitant.
    apply HPQ'.
    apply sinhabits.
    exact HP. }
  apply sinhabitant.
  exact (Hinstance Hprem).
Defined.

Instance Original_LF__DOT__Logic_LF_Logic_peirce_iso : Iso Original.LF_DOT_Logic.LF.Logic.peirce imported_Original_LF__DOT__Logic_LF_Logic_peirce.
Proof.
  unfold Original.LF_DOT_Logic.LF.Logic.peirce, imported_Original_LF__DOT__Logic_LF_Logic_peirce, Imported.Original_LF__DOT__Logic_LF_Logic_peirce.
  apply Build_Iso with (to := peirce_Prop_to_SProp) (from := peirce_SProp_to_Prop).
  - (* to_from: forall x, to (from x) = x, with = in SProp *)
    intro x.
    apply IsoEq.functional_extensionality_dep.
    intro P.
    apply IsoEq.functional_extensionality_dep.
    intro Q.
    apply IsoEq.functional_extensionality_dep.
    intro H.
    (* Now we need to show two things of type P : SProp are equal *)
    (* Since P : SProp, all its inhabitants are definitionally equal *)
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: forall x, from (to x) = x, with = in SProp *)
    intro x.
    apply IsoEq.functional_extensionality_dep.
    intro P.
    apply IsoEq.functional_extensionality_dep.
    intro Q.
    apply IsoEq.functional_extensionality_dep.
    intro H.
    (* Both sides are of type P : Prop, use proof irrelevance *)
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.peirce := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_peirce := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.peirce Original_LF__DOT__Logic_LF_Logic_peirce_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.peirce Imported.Original_LF__DOT__Logic_LF_Logic_peirce Original_LF__DOT__Logic_LF_Logic_peirce_iso := {}.