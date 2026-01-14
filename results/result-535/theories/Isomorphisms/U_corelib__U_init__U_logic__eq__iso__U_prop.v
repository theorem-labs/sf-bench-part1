From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
From Stdlib.Logic Require Import ProofIrrelevance.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq_Prop).

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  unfold rel_iso in *.
  simpl in *.
  
  (* Since x2 : SProp, all elements of x2 are equal *)
  (* Therefore x4 = x6, so Corelib_Init_Logic_eq_Prop x2 x4 x6 is inhabited *)
  (* Also, since from hx maps SProp to Type and all SProp elements are equal, *)
  (* from hx x4 = from hx x6, so x3 = x5 after using from_to *)
  
  pose proof (from_to hx x3) as Hft3.
  pose proof (from_to hx x5) as Hft5.
  
  (* x3 = x5 because from (to x3) = x3 and from (to x5) = x5, *)
  (* and to x3 = to x5 (as elements of SProp) *)
  assert (Heq : x3 = x5).
  { transitivity (from hx (to hx x3)).
    { symmetry. apply eq_of_seq. exact Hft3. }
    transitivity (from hx (to hx x5)).
    2:{ apply eq_of_seq. exact Hft5. }
    reflexivity. (* SProp equality *) }
  
  refine {|
    to := fun _ => Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4;
    from := fun _ => Heq;
    to_from := _;
    from_to := _
  |}.
  - intros e. apply IsomorphismDefinitions.eq_refl.
  - intros e. apply seq_of_eq. apply proof_irrelevance.
Defined.
Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
