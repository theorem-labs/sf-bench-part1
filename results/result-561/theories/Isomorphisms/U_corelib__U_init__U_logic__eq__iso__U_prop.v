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

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  (* This is an isomorphism between Prop (eq) and SProp (Corelib_Init_Logic_eq_Prop) *)
  (* Both are proof-irrelevant *)
  (* x2 : SProp means x4 and x6 are irrelevant, so eq_Prop x4 x6 is trivially true *)
  (* Also, any two elements of an SProp are definitionally equal *)
  
  (* Since x4 x6 : x2 : SProp, they are definitionally equal *)
  (* So Corelib_Init_Logic_eq_Prop x2 x4 x6 = Corelib_Init_Logic_eq_Prop x2 x4 x4 *)
  
  (* Define to direction *)
  assert (to_dir : Logic.eq x3 x5 -> Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6).
  { intro e. destruct e.
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4). }
  
  (* Define from direction: since Iso x1 x2 with x2 : SProp, all elements of x1 map to the same SProp element *)
  (* But this would mean x3 = x5 doesn't necessarily hold unless x1 has only one element... *)
  (* Actually, for a valid Iso between x1 : Type and x2 : SProp, x1 must be a subsingleton *)
  (* We can use the from_to property of the isomorphism *)
  assert (from_dir : Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 -> Logic.eq x3 x5).
  { intro e.
    (* from_to : from (to x) = x *)
    (* to x3 : x2, to x5 : x2, and since x2 : SProp, to x3 = to x5 *)
    (* Therefore from (to x3) = from (to x5) *)
    (* And by from_to, x3 = from (to x3) and x5 = from (to x5) *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    apply eq_of_seq in Hft3.
    apply eq_of_seq in Hft5.
    rewrite <- Hft3, <- Hft5.
    reflexivity. (* to x3 = to x5 in SProp *) }
  
  refine {|
    to := to_dir;
    from := from_dir;
    to_from := _;
    from_to := _
  |}.
  - (* to_from *)
    intros e. apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intros e. apply seq_of_eq. apply proof_irrelevance.
Defined.
Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
