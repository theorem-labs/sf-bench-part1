From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf__U_rel__relation__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf__U_rel__relation__iso Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso.

  Export Interface.U_original__U2_lf__U_rel__relation__iso.CodeBlocks Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks.

#[export] Instance: MustUnfold (@Original.LF.Rel.partial_function) := {}.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf__U_rel__relation__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface.

Module Type Interface (Import args : Args).

Definition imported_Original_LF_Rel_partial__function : forall x : Type, (x -> x -> SProp) -> SProp
  := fun (x : Type) (x0 : x -> x -> SProp) => forall a' a'0 a'1 : x, x0 a' a'0 -> x0 a' a'1 -> imported_Corelib_Init_Logic_eq a'0 a'1.
Definition Original_LF_Rel_partial__function_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF.Rel.relation x1) (x4 : x2 -> x2 -> SProp),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (x3 x5 x7) (x4 x6 x8)) ->
  Iso (Original.LF.Rel.partial_function x3) (imported_Original_LF_Rel_partial__function x4)
  := fun (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF.Rel.relation x1) (x4 : x2 -> x2 -> SProp)
    (hx0 : forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (x3 x5 x7) (x4 x6 x8)) =>
  IsoForall (fun a : x1 => forall y1 y2 : x1, x3 a y1 -> x3 a y2 -> y1 = y2) (fun x6 : x2 => forall a' a'0 : x2, x4 x6 a' -> x4 x6 a'0 -> imported_Corelib_Init_Logic_eq a' a'0)
    (fun (x5 : x1) (x6 : x2) (hx1 : rel_iso hx x5 x6) =>
     IsoForall (fun a : x1 => forall y2 : x1, x3 x5 a -> x3 x5 y2 -> a = y2) (fun x8 : x2 => forall a' : x2, x4 x6 x8 -> x4 x6 a' -> imported_Corelib_Init_Logic_eq x8 a')
       (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) =>
        IsoForall (fun a : x1 => x3 x5 x7 -> x3 x5 a -> x7 = a) (fun x10 : x2 => x4 x6 x8 -> x4 x6 x10 -> imported_Corelib_Init_Logic_eq x8 x10)
          (fun (x9 : x1) (x10 : x2) (hx3 : rel_iso hx x9 x10) => IsoArrow (hx0 x5 x6 hx1 x7 x8 hx2) (IsoArrow (hx0 x5 x6 hx1 x9 x10 hx3) (Corelib_Init_Logic_eq_iso hx2 hx3))))).
Existing Instance Original_LF_Rel_partial__function_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF.Rel.partial_function) ?x) => unify x Original_LF_Rel_partial__function_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF.Rel.partial_function) imported_Original_LF_Rel_partial__function ?x) => unify x Original_LF_Rel_partial__function_iso; constructor : typeclass_instances.


End Interface.