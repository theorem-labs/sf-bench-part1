From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

(* Note: we don't import the main eq_iso file here to avoid circular dependencies *)

(* The Imported.Corelib_Init_Logic_eq_Prop is for SProp equality *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Since we need equality in Prop but imported gives us SProp, we need to handle this carefully *)
(* For Prop case: the interface wants x1 : Type and x2 : SProp with Iso x1 x2 *)
Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)).
Proof.
  intros x1 x2 hx x3 x4 H34 x5 x6 H56.
  (* x3 = x5 is Prop, imported_Corelib_Init_Logic_eq_Prop x4 x6 is SProp *)
  unshelve eapply Build_Iso.
  - (* to: (x3 = x5) -> imported_Corelib_Init_Logic_eq_Prop x4 x6 *)
    intro Heq.
    destruct Heq.
    unfold imported_Corelib_Init_Logic_eq_Prop.
    (* Now x3 = x5, and we have H34 : to hx x3 = x4, H56 : to hx x3 = x6 *)
    (* We need Imported.Corelib_Init_Logic_eq_Prop x2 x4 x6 *)
    exact (eq_srect (A:=x2) (fun w => Imported.Corelib_Init_Logic_eq_Prop x2 w x6)
             (eq_srect (A:=x2) (fun w => Imported.Corelib_Init_Logic_eq_Prop x2 x4 w)
                (Imported.Corelib_Init_Logic_eq_Prop_refl x2 x4) 
                (eq_trans (eq_sym H34) H56))
             IsomorphismDefinitions.eq_refl).
  - (* from: imported_Corelib_Init_Logic_eq_Prop x4 x6 -> (x3 = x5) *)
    intro Heq.
    apply eq_of_seq.
    pose proof (from_to hx x3) as Hx3.
    pose proof (from_to hx x5) as Hx5.
    pose proof (f_equal (from hx) H34) as Hf34.
    pose proof (f_equal (from hx) H56) as Hf56.
    pose proof (Imported.Corelib_Init_Logic_eq_Prop_indl x2 x4
      (fun z _ => IsomorphismDefinitions.eq x4 z)
      IsomorphismDefinitions.eq_refl x6 Heq) as Heq'.
    pose proof (f_equal (from hx) Heq') as HfromHeq.
    apply (eq_trans (eq_sym Hx3)).
    apply (eq_trans Hf34).
    apply (eq_trans HfromHeq).
    apply (eq_trans (eq_sym Hf56)).
    exact Hx5.
  - (* to_from: SProp proof irrelevance *)
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
