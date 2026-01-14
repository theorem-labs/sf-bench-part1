From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso.
From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso__U_prop.

Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq).

(* Helper: Imported eq is an equivalence relation - we can transport using isomorphism injectivity *)
Definition imported_eq_from_eq {A B : Type} (i : Iso A B) {x y : A} (H : x = y) : 
  Imported.Corelib_Init_Logic_eq B (to i x) (to i y) :=
  match H in Logic.eq _ z return Imported.Corelib_Init_Logic_eq B (to i x) (to i z) with
  | Logic.eq_refl => Imported.Corelib_Init_Logic_eq_refl B (to i x)
  end.

Definition eq_from_imported_eq {A B : Type} (i : Iso A B) {x y : A} 
  (H : Imported.Corelib_Init_Logic_eq B (to i x) (to i y)) : x = y.
Proof.
  (* Use injectivity of 'to' via round-trip *)
  assert (from i (to i x) = from i (to i y)) as Hf.
  { destruct H. reflexivity. }
  rewrite (eq_of_seq (from_to i x)) in Hf.
  rewrite (eq_of_seq (from_to i y)) in Hf.
  exact Hf.
Defined.

(* Isomorphism between Prop eq and SProp eq. *)
Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 h34 x5 x6 h56.
  unfold imported_Corelib_Init_Logic_eq.
  unfold rel_iso in *.
  destruct h34, h56.
  (* Now we need Iso (x3 = x5) (Imported.Corelib_Init_Logic_eq x2 (to hx x3) (to hx x5)) *)
  unshelve eapply Build_Iso.
  - (* to *) exact (imported_eq_from_eq hx).
  - (* from *) exact (eq_from_imported_eq hx).
  - (* to_from *) intro x. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *) intro x.
    (* Use proof irrelevance: both are proofs of x3 = x5, which is a Prop *)
    apply seq_of_eq.
    apply Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
Defined.
Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.