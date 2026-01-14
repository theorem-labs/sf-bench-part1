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

(* The Prop version of eq needs to handle SProp on the imported side *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := (@Imported.Corelib_Init_Logic_eq_Prop).

(* For the Prop case, x1 : Type and x2 : SProp, but we need to build iso
   between (x3 = x5 : Prop) and Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 : SProp
   
   Since both are propositions, the isomorphism is trivial by proof irrelevance.
   We just need to show they are both inhabited or both empty.
   
   Since x4 and x6 come from an isomorphism applied to x3 and x5, 
   x3 = x5 iff x4 = x6.
*)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unfold imported_Corelib_Init_Logic_eq_Prop.
  
  (* The to direction: if x3 = x5 then x4 = x6 *)
  assert (to_dir : Logic.eq x3 x5 -> Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6).
  { intro e. destruct e.
    (* H34 and H56 both say the isomorphism maps x3 to something *)
    (* Since x3 = x5, H34 : to x3 = x4 and H56 : to x3 = x6, so x4 = x6 *)
    apply Imported.Corelib_Init_Logic_eq_Prop_refl. }
  
  (* The from direction: if x4 = x6 then x3 = x5 *)
  (* But we can't directly destruct an SProp equality for a Type goal.
     Instead, we use the isomorphism: x3 = from x4 and x5 = from x6.
     If x4 = x6 in SProp, then from x4 = from x6 in Type.
     But we need to show this using the proof irrelevance trick. *)
  assert (from_dir : Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 -> Logic.eq x3 x5).
  { intro e.
    (* e says x4 = x6 in SProp. We need x3 = x5 in Prop. *)
    (* x3 = from (to x3) = from x4 (using H34) *)
    (* x5 = from (to x5) = from x6 (using H56) *)
    pose proof (from_to hx x3) as FT3.
    pose proof (from_to hx x5) as FT5.
    transitivity (from hx (to hx x3)).
    { symmetry. exact (eq_of_seq FT3). }
    transitivity (from hx (to hx x5)).
    2:{ exact (eq_of_seq FT5). }
    (* Now we need: from (to x3) = from (to x5) *)
    (* We know to x3 = x4 (H34) and to x5 = x6 (H56) *)
    (* And e tells us x4 = x6 in SProp *)
    (* But from : x2 -> x1 where x2 : SProp, so from can't distinguish x4 from x6 *)
    (* Actually, from has type x2 -> x1, and x4 x6 : x2 where x2 is an SProp.
       In SProp, any two inhabitants are equal. So from x4 = from x6 in Type. *)
    reflexivity. }
  
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
