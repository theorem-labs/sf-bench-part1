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

(* For the SProp case, x2 is an SProp and x4, x6 : x2 are both inhabitants of the same SProp.
   Any two inhabitants of an SProp are definitionally equal. So Corelib_Init_Logic_eq_Prop x2 x4 x6 
   is always inhabited by refl.
   The tricky part is showing x3 = x5. Since we have an Iso between x1 and x2 (an SProp),
   and x1 : Type, this means x1 essentially has at most one inhabitant up to equality
   (since it's isomorphic to an SProp). *)

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  
  (* to direction: x3 = x5 -> Corelib_Init_Logic_eq_Prop x2 x4 x6 *)
  (* The target is an SProp, so any proof works *)
  assert (to_dir : Logic.eq x3 x5 -> Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6).
  { intro e.
    (* In SProp, x4 and x6 are definitionally equal since they're both terms of the SProp x2 *)
    exact (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4). }
  
  (* from direction: Corelib_Init_Logic_eq_Prop x2 x4 x6 -> x3 = x5 *)
  (* Since x1 is isomorphic to an SProp, all elements of x1 are equal *)
  assert (from_dir : Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 -> Logic.eq x3 x5).
  { intro e.
    (* x3 = from (to x3) and x5 = from (to x5) *)
    (* But to x3 : x2 and to x5 : x2, and x2 : SProp, so to x3 = to x5 definitionally *)
    (* Hence from (to x3) = from (to x5) *)
    pose proof (from_to hx x3) as Hft3.
    pose proof (from_to hx x5) as Hft5.
    (* Hft3 : from (to x3) = x3, Hft5 : from (to x5) = x5 in SProp eq *)
    transitivity (from hx (to hx x3)).
    { symmetry. apply eq_of_seq. exact Hft3. }
    transitivity (from hx (to hx x5)).
    2:{ apply eq_of_seq. exact Hft5. }
    (* Now: from (to x3) = from (to x5) *)
    (* Since x2 : SProp, to x3 and to x5 are definitionally equal *)
    reflexivity. }
  
  refine {|
    to := to_dir;
    from := from_dir;
    to_from := _;
    from_to := _
  |}.
  - intros e. apply IsomorphismDefinitions.eq_refl.
  - intros e. apply seq_of_eq. apply proof_irrelevance.
Defined.
