From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


(* Define the imported list type manually since it's not in Imported.v *)
Inductive imported_Original_LF__DOT__Poly_LF_Poly_list (A : Type) : Type :=
  | Original_LF__DOT__Poly_LF_Poly_list_nil : imported_Original_LF__DOT__Poly_LF_Poly_list A
  | Original_LF__DOT__Poly_LF_Poly_list_cons : A -> imported_Original_LF__DOT__Poly_LF_Poly_list A -> imported_Original_LF__DOT__Poly_LF_Poly_list A.

Arguments Original_LF__DOT__Poly_LF_Poly_list_nil {A}.
Arguments Original_LF__DOT__Poly_LF_Poly_list_cons {A} _ _.
Instance Original_LF__DOT__Poly_LF_Poly_list_iso : forall x1 x2 : Type, Iso x1 x2 -> Iso (Original.LF_DOT_Poly.LF.Poly.list x1) (imported_Original_LF__DOT__Poly_LF_Poly_list x2).
Proof.
  intros x1 x2 Hx.
  unshelve eapply Build_Iso.
  - (* to: Original.list x1 -> imported list x2 *)
    exact (fix to_list (l : Original.LF_DOT_Poly.LF.Poly.list x1) : imported_Original_LF__DOT__Poly_LF_Poly_list x2 :=
      match l with
      | Original.LF_DOT_Poly.LF.Poly.nil => Original_LF__DOT__Poly_LF_Poly_list_nil
      | Original.LF_DOT_Poly.LF.Poly.cons h t => 
          Original_LF__DOT__Poly_LF_Poly_list_cons (to Hx h) (to_list t)
      end).
  - (* from: imported list x2 -> Original.list x1 *)
    exact (fix from_list (l : imported_Original_LF__DOT__Poly_LF_Poly_list x2) : Original.LF_DOT_Poly.LF.Poly.list x1 :=
      match l with
      | Original_LF__DOT__Poly_LF_Poly_list_nil => Original.LF_DOT_Poly.LF.Poly.nil
      | Original_LF__DOT__Poly_LF_Poly_list_cons h t => 
          Original.LF_DOT_Poly.LF.Poly.cons (from Hx h) (from_list t)
      end).
  - (* to_from *)
    intro l.
    induction l as [|h t IH].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl. 
      apply (IsoEq.f_equal2 (@Original_LF__DOT__Poly_LF_Poly_list_cons x2) (to_from Hx h) IH).
  - (* from_to *)
    intro l.
    induction l as [|h t IH].
    + apply IsomorphismDefinitions.eq_refl.
    + simpl.
      apply (IsoEq.f_equal2 (@Original.LF_DOT_Poly.LF.Poly.cons x1) (from_to Hx h) IH).
Defined.
Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.list := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant imported_Original_LF__DOT__Poly_LF_Poly_list := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.list Original_LF__DOT__Poly_LF_Poly_list_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.list imported_Original_LF__DOT__Poly_LF_Poly_list Original_LF__DOT__Poly_LF_Poly_list_iso := {}.