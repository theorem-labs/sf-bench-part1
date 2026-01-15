From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From Stdlib Require Import ProofIrrelevance.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.

Definition imported_Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not : SProp := Imported.Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not.

(* Helper: de_morgan_to converts from Prop version to SProp version *)
Definition de_morgan_to : 
  Original.LF_DOT_Logic.LF.Logic.de_morgan_not_and_not ->
  imported_Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not.
Proof.
  intro H.
  intros P Q Hpq.
  assert (Hres : inhabited P \/ inhabited Q).
  { apply H.
    intro contra. destruct contra as [Hninp Hninq].
    (* Hpq : Imported.and (...) -> Imported.False *)
    (* Need to prove False : Prop from Imported.False : SProp *)
    (* Use inhabited on Imported.False and destruct *)
    assert (Hfalse : inhabited Imported.False).
    { constructor. apply Hpq.
      split.
      - intro p. destruct (Hninp (inhabits p)).
      - intro q. destruct (Hninq (inhabits q)).
    }
    destruct Hfalse as [[]].
  }
  destruct Hres as [[p] | [q]].
  - left. exact p.
  - right. exact q.
Defined.

(* Helper to convert SProp or to SInhabited (Prop or) *)
Definition or_sprop_to_sinhabited (P Q : Prop) : Imported.or (SInhabited P) (SInhabited Q) -> SInhabited (P \/ Q).
Proof.
  intro Hor.
  destruct Hor as [sp | sq].
  - exact (sinhabits (or_introl (sinhabitant sp))).
  - exact (sinhabits (or_intror (sinhabitant sq))).
Defined.

(* Helper: de_morgan_from converts from SProp version to Prop version *)
Definition de_morgan_from : 
  imported_Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not ->
  Original.LF_DOT_Logic.LF.Logic.de_morgan_not_and_not.
Proof.
  intro H.
  intros P Q Hpq.
  assert (Hres : Imported.or (SInhabited P) (SInhabited Q)).
  { apply H.
    intro contra. destruct contra as [Hninp Hninq].
    (* Hninp : SInhabited P -> Imported.False *)
    (* Hninq : SInhabited Q -> Imported.False *)
    (* Hpq : ~ P /\ ~ Q -> False *)
    (* Need to show Imported.False *)
    assert (HF : False).
    { apply Hpq.
      split.
      - intro p. 
        assert (Hif : inhabited Imported.False).
        { constructor. apply Hninp. exact (sinhabits p). }
        destruct Hif as [[]].
      - intro q.
        assert (Hif : inhabited Imported.False).
        { constructor. apply Hninq. exact (sinhabits q). }
        destruct Hif as [[]].
    }
    destruct HF.
  }
  (* Use the helper to convert SProp or to SInhabited, then sinhabitant *)
  exact (sinhabitant (or_sprop_to_sinhabited Hres)).
Defined.

#[local] Unset Universe Polymorphism.
Instance Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not_iso : Iso Original.LF_DOT_Logic.LF.Logic.de_morgan_not_and_not imported_Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not.
Proof.
  unshelve econstructor.
  - exact de_morgan_to.
  - exact de_morgan_from.
  - intro x. apply IsomorphismDefinitions.eq_refl.
  - intro x. apply seq_of_eq. apply proof_irrelevance.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.de_morgan_not_and_not := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.de_morgan_not_and_not Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.de_morgan_not_and_not Imported.Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not Original_LF__DOT__Logic_LF_Logic_de__morgan__not__and__not_iso := {}.