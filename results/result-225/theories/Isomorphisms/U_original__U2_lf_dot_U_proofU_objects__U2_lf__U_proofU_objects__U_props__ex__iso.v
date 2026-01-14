From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

Require Import Stdlib.Logic.ProofIrrelevance.

Definition imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex : forall x : Type, (x -> SProp) -> SProp := (@Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex).

(* Helper to convert Original.ex to Imported.ex *)
Definition ex_to_imported {A1 A2 : Type} {P1 : A1 -> Prop} {P2 : A2 -> SProp}
    (iso_A : Iso A1 A2)
    (iso_P : forall (a1 : A1) (a2 : A2), rel_iso iso_A a1 a2 -> Iso (P1 a1) (P2 a2))
    (e : Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex P1)
    : Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex A2 P2 :=
  match e with
  | Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex_intro _ x pf =>
      Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_ex_intro A2 P2
        (iso_A.(to) x)
        ((iso_P x (iso_A.(to) x) (IsomorphismDefinitions.eq_refl)).(to) pf)
  end.

(* For converting from SProp ex to Prop ex, we use the SInhabited mechanism *)
(* Key insight: if we have Imported.ex P2 (in SProp), we can get Original.ex P1 (in Prop)
   by using the fact that both represent the same logical content *)

Definition ex_from_imported {A1 A2 : Type} {P1 : A1 -> Prop} {P2 : A2 -> SProp}
    (iso_A : Iso A1 A2)
    (iso_P : forall (a1 : A1) (a2 : A2), rel_iso iso_A a1 a2 -> Iso (P1 a1) (P2 a2))
    (e : Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex A2 P2)
    : Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex P1.
Proof.
  (* We use indl to get an SInhabited of the result, then sinhabitant to get the Prop *)
  apply sinhabitant.
  apply (Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_indl A2 P2
    (fun _ => SInhabited (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex P1))).
  - intros x2 pf2.
    apply sinhabits.
    set (x1 := iso_A.(from) x2).
    (* We need an iso between P1 x1 and P2 x2 *)
    (* rel_iso iso_A x1 x2 means: to iso_A x1 = x2 *)
    (* We have: to_from iso_A x2 : to (from x2) = x2 *)
    (* So: to iso_A x1 = to iso_A (from iso_A x2) = x2 by to_from *)
    assert (Hrel : rel_iso iso_A x1 x2).
    { unfold rel_iso, x1. simpl. apply iso_A.(to_from). }
    set (the_iso := iso_P x1 x2 Hrel).
    exact (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex_intro P1 x1 (the_iso.(from) pf2)).
  - exact e.
Defined.

Instance Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1 -> Prop) (x4 : x2 -> SProp),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 x5) (x4 x6)) ->
  Iso (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex x3) (imported_Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex x4).
Proof.
  intros A1 A2 iso_A P1 P2 iso_P.
  refine (@Build_Iso 
           (Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex P1)
           (Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex A2 P2)
           (@ex_to_imported A1 A2 P1 P2 iso_A iso_P)
           (@ex_from_imported A1 A2 P1 P2 iso_A iso_P)
           (fun _ => IsomorphismDefinitions.eq_refl)
           _).
  (* from_to: need eq (ex_from_imported (ex_to_imported e)) e *)
  intro e.
  (* Both are proofs of ex P1, use proof irrelevance *)
  pose proof (proof_irrelevance _ (@ex_from_imported A1 A2 P1 P2 iso_A iso_P (@ex_to_imported A1 A2 P1 P2 iso_A iso_P e)) e) as H.
  destruct H.
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex) Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_ProofObjects.LF.ProofObjects.Props.ex) (@Imported.Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex) Original_LF__DOT__ProofObjects_LF_ProofObjects_Props_ex_iso := {}.