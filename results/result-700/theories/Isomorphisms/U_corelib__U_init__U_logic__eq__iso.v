From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq is now in SProp (defined in Prop in Lean) *)
Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq.

(* Helper: extract Logic.eq from Imported.Corelib_Init_Logic_eq *)
Definition seq_to_eq {A : Type} {x y : A} (H : Imported.Corelib_Init_Logic_eq A x y) : x = y :=
  match H with Imported.Corelib_Init_Logic_eq_refl _ _ => Logic.eq_refl end.

(* Helper lemma: isomorphisms are injective *)
Lemma iso_injective : forall (A B : Type) (i : Iso A B) (x y : A),
  to i x = to i y -> x = y.
Proof.
  intros A B i x y H.
  rewrite <- (from_to i x).
  rewrite <- (from_to i y).
  apply Logic.f_equal. exact H.
Qed.

(* We define the isomorphism by providing explicit functions *)
Definition eq_iso_to (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2) (H56 : IsomorphismDefinitions.eq (to hx x5) x6)
  : x3 = x5 -> imported_Corelib_Init_Logic_eq x4 x6.
Proof.
  intro Heq.
  destruct H34. destruct H56. destruct Heq.
  exact (Imported.Corelib_Init_Logic_eq_refl _ _).
Defined.

Definition eq_iso_from (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2) (H56 : IsomorphismDefinitions.eq (to hx x5) x6)
  : imported_Corelib_Init_Logic_eq x4 x6 -> x3 = x5.
Proof.
  intro Hseq.
  destruct H34. destruct H56.
  apply (@iso_injective x1 x2 hx x3 x5).
  apply seq_to_eq. exact Hseq.
Defined.

From Stdlib Require Import Logic.Eqdep_dec.

(* Use proof irrelevance to handle all equality proofs *)
Lemma eq_proofs_equal : forall (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intros A x y p q.
  apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Qed.

Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold rel_iso in H34, H56.
  unshelve eapply Build_Iso.
  + exact (@eq_iso_to x1 x2 hx x3 x4 H34 x5 x6 H56).
  + exact (@eq_iso_from x1 x2 hx x3 x4 H34 x5 x6 H56).
  + intro Hseq.
    reflexivity.
  + intro Heq.
    destruct H34. destruct H56. destruct Heq.
    unfold eq_iso_from, eq_iso_to. simpl.
    rewrite (@eq_proofs_equal x1 x3 x3 (iso_injective hx x3 x3 Logic.eq_refl) Logic.eq_refl).
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.

(* Module for Prop-level equality isomorphism *)
Module U_corelib__U_init__U_logic__eq__iso__U_prop.

(* Imported.Corelib_Init_Logic_eq_Prop is now in SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Use match on the SProp eq to get that the two to i x and to i y are definitionally equal *)
Definition from_seq_Prop {A : Type} {B : SProp} (i : Iso A B) {x y : A}
  (H : Imported.Corelib_Init_Logic_eq_Prop B (to i x) (to i y)) : x = y :=
  match H in (Imported.Corelib_Init_Logic_eq_Prop _ _ z) return (from i (to i x) = from i z) -> x = y with
  | Imported.Corelib_Init_Logic_eq_Prop_refl _ _ => fun pf =>
      match from_to i x in IsomorphismDefinitions.eq _ w return w = y with
      | IsomorphismDefinitions.eq_refl =>
        match from_to i y in IsomorphismDefinitions.eq _ w return from i (to i x) = w with
        | IsomorphismDefinitions.eq_refl => pf
        end
      end
  end Logic.eq_refl.

(* Build Iso using proof irrelevance for the roundtrip conditions *)
Definition Corelib_Init_Logic_eq_iso_Prop_aux (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6)
   : Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6).
Proof.
  unfold rel_iso in H34, H56.
  pose (fwd := fun (Heq : x3 = x5) =>
    match H34 in (IsomorphismDefinitions.eq _ y4) return imported_Corelib_Init_Logic_eq_Prop y4 x6 with
    | IsomorphismDefinitions.eq_refl =>
      match H56 in (IsomorphismDefinitions.eq _ y6) return imported_Corelib_Init_Logic_eq_Prop (to hx x3) y6 with
      | IsomorphismDefinitions.eq_refl =>
        match Heq in (_ = y5) return imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx y5) with
        | Logic.eq_refl => Imported.Corelib_Init_Logic_eq_Prop_refl _ _
        end
      end
    end).
  pose (bwd := fun (Hseq : imported_Corelib_Init_Logic_eq_Prop x4 x6) =>
    match H34 in (IsomorphismDefinitions.eq _ y4) return (imported_Corelib_Init_Logic_eq_Prop y4 x6 -> x3 = x5) with
    | IsomorphismDefinitions.eq_refl => fun Hseq' =>
      match H56 in (IsomorphismDefinitions.eq _ y6) return (imported_Corelib_Init_Logic_eq_Prop (to hx x3) y6 -> x3 = x5) with
      | IsomorphismDefinitions.eq_refl => fun Hseq'' => from_seq_Prop hx Hseq''
      end Hseq'
    end Hseq).
  unshelve eapply Build_Iso.
  - exact fwd.
  - exact bwd.
  - intro Hseq. reflexivity.
  - intro Heq. 
    (* Both sides are x3 = x5 in Prop, need SProp eq between them *)
    (* We use the sinhabitant approach to show any two Prop proofs are SProp-equal *)
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ (bwd (fwd Heq)) Heq) as PIR.
    destruct PIR.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)) :=
  Corelib_Init_Logic_eq_iso_Prop_aux.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.

End U_corelib__U_init__U_logic__eq__iso__U_prop.

(* Require the separate _U_prop file so it's loaded when this file is required *)
From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso__U_prop.
