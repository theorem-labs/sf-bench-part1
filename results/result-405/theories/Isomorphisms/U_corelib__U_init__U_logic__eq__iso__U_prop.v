From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib.Logic Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq_Prop).

(* For Prop types: x1 is a Type that represents propositions, x2 is SProp *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  
  (* Define to direction *)
  assert (to_dir : Logic.eq x3 x5 -> Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6).
  { intro e. destruct e.
    (* Now x3 = x5, so x4 and x6 are both related to the same element *)
    (* In SProp, all inhabitants are equal, so use eq_refl *)
    apply Imported.Corelib_Init_Logic_eq_Prop_refl. }
  
  (* Define from direction *)
  assert (from_dir : Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 -> Logic.eq x3 x5).
  { intro e.
    (* Use the isomorphism to show x3 = x5 *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    transitivity (from hx (to hx x3)).
    { symmetry. apply eq_of_seq. exact Hft3. }
    transitivity (from hx (to hx x5)).
    2:{ apply eq_of_seq. exact Hft5. }
    (* Now need: from (to x3) = from (to x5) *)
    (* to x3 = x4 and to x5 = x6 from H34 and H56 *)
    (* In SProp, x4 and x6 are definitionally equal *)
    reflexivity. }
  
  refine {|
    to := to_dir;
    from := from_dir;
    to_from := _;
    from_to := _
  |}.
  - (* to_from: proof irrelevance in SProp *)
    intros e. apply IsomorphismDefinitions.eq_refl.
  - (* from_to: use proof irrelevance *)
    intros e. apply seq_of_eq. apply proof_irrelevance.
Defined.
Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}. (* only needed when rel_iso is typeclasses opaque *)
