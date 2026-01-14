From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
From LeanImport Require Import Lean.

Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Imported.

Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq.

(* For equality, we build an Iso between Prop and SProp types. *)
(* The key insight is that both sides are proof-irrelevant, so we can use the relation
   hypotheses to build witnesses. *)

Lemma eq_iso_to (x1 x2 : Type) (hx : Iso x1 x2) (x3 x5 : x1) (x4 x6 : x2)
  (h34 : @rel_iso x1 x2 hx x3 x4) (h56 : @rel_iso x1 x2 hx x5 x6) :
  x3 = x5 -> imported_Corelib_Init_Logic_eq x4 x6.
Proof.
  intro H. destruct H.
  (* h34 : IsomorphismDefinitions.eq (to hx x3) x4 *)
  (* h56 : IsomorphismDefinitions.eq (to hx x3) x6 *)
  (* Want: Imported.Corelib_Init_Logic_eq x2 x4 x6 *)
  refine (@eq_srect x2 (to hx x3) (fun z => Imported.Corelib_Init_Logic_eq x2 z x6) _ x4 h34).
  refine (@eq_srect x2 (to hx x3) (fun z => Imported.Corelib_Init_Logic_eq x2 (to hx x3) z) _ x6 h56).
  exact (Imported.Corelib_Init_Logic_eq_refl x2 (to hx x3)).
Defined.

Lemma eq_iso_from (x1 x2 : Type) (hx : Iso x1 x2) (x3 x5 : x1) (x4 x6 : x2)
  (h34 : @rel_iso x1 x2 hx x3 x4) (h56 : @rel_iso x1 x2 hx x5 x6) :
  imported_Corelib_Init_Logic_eq x4 x6 -> x3 = x5.
Proof.
  intro H. destruct H.
  apply eq_of_seq.
  pose proof (from_to hx x3) as H3.
  pose proof (from_to hx x5) as H5.
  pose proof (f_equal (from hx) h34) as Hf34.
  pose proof (f_equal (from hx) h56) as Hf56.
  apply (eq_trans (eq_sym H3)).
  apply (eq_trans Hf34).
  apply (eq_trans (eq_sym Hf56)).
  exact H5.
Defined.

Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 h34 x5 x6 h56.
  refine (Build_Iso (@eq_iso_to x1 x2 hx x3 x5 x4 x6 h34 h56) (@eq_iso_from x1 x2 hx x3 x5 x4 x6 h34 h56) _ _).
  - (* to_from *)
    intro q. destruct q. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: need IsomorphismDefinitions.eq (from (to p)) p *)
    intro p. apply sUIPt.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.
