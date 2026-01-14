From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* The Imported.Corelib_Init_Logic_eq_Prop for SProp-typed arguments *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Isomorphism between eq (for Prop -> Type) and eq_Prop (for SProp -> SProp) 
   The interface signature is:
   forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) ... *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  unshelve eapply Build_Iso.
  - (* to: x3 = x5 (in Prop) -> Imported eq x4 x6 (in SProp) *)
    intro Heq.
    destruct Heq.
    (* Now x3 = x5, and we have H34 : to hx x3 = x4, H56 : to hx x5 = x6 *)
    (* So x4 = to hx x3 = to hx x5 = x6 *)
    unfold imported_Corelib_Init_Logic_eq_Prop.
    (* We need Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 *)
    (* Since H34 : eq (to hx x3) x4 and H56 : eq (to hx x3) x6, we have x4 = x6 via transitivity *)
    pose proof (IsoEq.eq_trans (IsoEq.eq_sym H34) H56) as Heq46.
    (* Heq46 : eq x4 x6 in SProp *)
    exact (IsoEq.eq_srect (fun w => Imported.Corelib_Init_Logic_eq_Prop x2 x4 w) 
             (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4) Heq46).
  - (* from: Imported eq x4 x6 -> x3 = x5 (in Prop) *)
    intro Heq.
    (* Use proof irrelevance / inhabitedness via functional approach *)
    pose proof (from_to hx x3) as Hx3.  (* eq (from hx (to hx x3)) x3 *)
    pose proof (from_to hx x5) as Hx5.  (* eq (from hx (to hx x5)) x5 *)
    pose proof (IsoEq.f_equal (from hx) H34) as Hf34. (* eq (from hx (to hx x3)) (from hx x4) *)
    pose proof (IsoEq.f_equal (from hx) H56) as Hf56. (* eq (from hx (to hx x5)) (from hx x6) *)
    (* Heq tells us x4 = x6 in SProp *)
    pose proof (Imported.Corelib_Init_Logic_eq_Prop_indl x2 x4 
      (fun z _ => IsomorphismDefinitions.eq x4 z) 
      IsomorphismDefinitions.eq_refl x6 Heq) as HfeqHeq. (* eq x4 x6 *)
    pose proof (IsoEq.f_equal (from hx) HfeqHeq) as HfromHeq. (* eq (from hx x4) (from hx x6) *)
    (* x3 = from hx (to hx x3) = from hx x4 = from hx x6 = from hx (to hx x5) = x5 *)
    apply IsoEq.eq_of_seq.
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hx3)).
    apply (IsoEq.eq_trans Hf34).
    apply (IsoEq.eq_trans HfromHeq).
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hf56)).
    exact Hx5.
  - (* to_from: in SProp, all proofs are equal *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to: Prop proofs can use destruct *)
    intro Heq.
    destruct Heq.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}.
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofFor (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
