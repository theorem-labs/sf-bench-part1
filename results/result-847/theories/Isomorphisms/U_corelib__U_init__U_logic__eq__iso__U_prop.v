From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* The Imported.Corelib_Init_Logic_eq_Prop is for SProp arguments *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* For Prop-sorted eq, we have an isomorphism between Prop and SProp *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* This is a cross-universe isomorphism between eq (Prop) and eq_Prop (SProp) *)
  unshelve eapply Build_Iso.
  - (* to: eq in Prop -> eq_Prop in SProp *)
    intro Heq.
    destruct Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    (* H34 and H56 are proofs relating x3,x4 and x5,x6 via the isomorphism
       Since x3 = x5 (after destruct), we need eq_Prop x4 x6 *)
    (* We use transport via the isomorphism *)
    pose proof (IsoEq.eq_srect (fun w => Imported.Corelib_Init_Logic_eq_Prop x2 w x6)
                  (IsoEq.eq_srect (fun w => Imported.Corelib_Init_Logic_eq_Prop x2 x4 w)
                    (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4) H56) H34) as result.
    exact result.
  - (* from: eq_Prop in SProp -> eq in Prop *)
    intro Heq.
    pose proof (from_to hx x3) as Hx3.
    pose proof (from_to hx x5) as Hx5.
    pose proof (IsoEq.f_equal (from hx) H34) as Hf34.
    pose proof (IsoEq.f_equal (from hx) H56) as Hf56.
    (* Convert Heq to IsomorphismDefinitions.eq *)
    pose proof (Imported.Corelib_Init_Logic_eq_Prop_indl x2 x4
      (fun z _ => IsomorphismDefinitions.eq x4 z)
      IsomorphismDefinitions.eq_refl x6 Heq) as HfeqHeq.
    pose proof (IsoEq.f_equal (from hx) HfeqHeq) as HfromHeq.
    apply IsoEq.eq_of_seq.
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hx3)).
    apply (IsoEq.eq_trans Hf34).
    apply (IsoEq.eq_trans HfromHeq).
    apply (IsoEq.eq_trans (IsoEq.eq_sym Hf56)).
    exact Hx5.
  - (* to_from *)
    intro Heq.
    apply IsomorphismDefinitions.eq_refl.
  - (* from_to *)
    intro Heq.
    destruct Heq.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant (@Corelib.Init.Logic.eq) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
