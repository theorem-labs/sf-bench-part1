From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.
From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso__U_prop.

(* Corelib_Init_Logic_eq in Imported is in SProp *)
Definition imported_Corelib_Init_Logic_eq : forall x : Type, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq.

(* Define the forward map *)
Definition eq_forward (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) 
  (Hx34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2)
  (Hx56 : IsomorphismDefinitions.eq (to hx x5) x6) 
  (pf : x3 = x5) : Imported.Corelib_Init_Logic_eq x2 x4 x6 :=
  eq_srect (fun z => Imported.Corelib_Init_Logic_eq x2 x4 z) 
    (eq_srect (fun z => Imported.Corelib_Init_Logic_eq x2 z (to hx x5))
      (match pf in (_ = z) return Imported.Corelib_Init_Logic_eq x2 (to hx x3) (to hx z) with
       | Logic.eq_refl => Imported.Corelib_Init_Logic_eq_refl x2 (to hx x3)
       end)
      Hx34)
    Hx56.

(* For the backward map, we use the SProp eliminator to produce x3 = x5.
   The input is Imported.Corelib_Init_Logic_eq x2 x4 x6 which lives in SProp.
   We CAN eliminate SProp to SProp, but we need Prop (x3 = x5).
   
   Key insight: we can use the fact that if pf : Imported.Corelib_Init_Logic_eq x2 x4 x6
   then x4 and x6 are "equal" in the imported sense, but we need to convert this.
   
   Actually - we can match on the SProp value when producing SProp or when the
   output type doesn't depend on the value. Let's try matching. *)

(* We need to match on the imported eq to get x4 = x6, then use from hx to get x3 = x5 *)
Definition eq_backward (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) 
  (Hx34 : IsomorphismDefinitions.eq (to hx x3) x4) (x5 : x1) (x6 : x2)
  (Hx56 : IsomorphismDefinitions.eq (to hx x5) x6)
  (pf : Imported.Corelib_Init_Logic_eq x2 x4 x6) : x3 = x5.
Proof.
  (* Transport H34 and H56 to get from hx x4 = x3 and from hx x6 = x5 *)
  pose (H34' := eq_srect (fun z => IsomorphismDefinitions.eq (from hx z) x3) (from_to hx x3) Hx34).
  pose (H56' := eq_srect (fun z => IsomorphismDefinitions.eq (from hx z) x5) (from_to hx x5) Hx56).
  (* We have H34' : eq (from hx x4) x3 *)
  (* We have H56' : eq (from hx x6) x5 *)
  (* We need to show x3 = x5 *)
  (* x3 = from hx x4 (by eq_sym H34') *)
  (* x5 = from hx x6 (by eq_sym H56') *)
  (* So x3 = x5 iff from hx x4 = from hx x6, which follows from x4 = x6 *)
  (* But x4 = x6 comes from pf, but pf is in SProp... *)
  
  (* Match on pf to refine x6 to x4 *)
  destruct pf.
  (* Now x6 is replaced by x4 (both point to the same), but Hx56 also changes *)
  (* After destruct, H34' : IsomorphismDefinitions.eq (from hx x4) x3 *)
  (* After destruct, H56' : IsomorphismDefinitions.eq (from hx x4) x5 *)
  (* We need x3 = x5 (Prop eq) *)
  
  (* eq_srect (fun z => z = x5) : (from hx x4 = x5) -> eq (from hx x4) x3 -> (x3 = x5) *)
  (* eq_srect (fun z => from hx x4 = z) : (from hx x4 = from hx x4) -> eq (from hx x4) x5 -> (from hx x4 = x5) *)
  
  (* Start: Logic.eq_refl : from hx x4 = from hx x4 *)
  (* Apply eq_srect with H56' to get: from hx x4 = x5 *)
  pose (step1 := eq_srect (fun z => from hx x4 = z) Logic.eq_refl H56').
  (* step1 : from hx x4 = x5 *)
  
  (* Apply eq_srect with H34' to transport the left side *)
  (* eq_srect (fun z => z = x5) step1 H34' : x3 = x5 *)
  exact (eq_srect (fun z => z = x5) step1 H34').
Defined.

Instance Corelib_Init_Logic_eq_iso : (forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 Hx34 x5 x6 Hx56.
  unfold rel_iso in *.
  unfold imported_Corelib_Init_Logic_eq.
  (* Build_Iso: to from to_from from_to *)
  (* to : (x3 = x5) -> Imported.Corelib_Init_Logic_eq x2 x4 x6 *)
  (* from : Imported.Corelib_Init_Logic_eq x2 x4 x6 -> (x3 = x5) *)
  (* to_from : forall y, to (from y) = y *)
  (* from_to : forall x, from (to x) = x *)
  exact (Build_Iso 
    (@eq_forward x1 x2 hx x3 x4 Hx34 x5 x6 Hx56) 
    (@eq_backward x1 x2 hx x3 x4 Hx34 x5 x6 Hx56)
    (fun _ => IsomorphismDefinitions.eq_refl)  (* to_from - SProp target, eq_refl works *)
    (fun e => sUIPt _ e)).  (* from_to - use proof irrelevance for Prop equality *)
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq) Corelib_Init_Logic_eq_iso := {}.
