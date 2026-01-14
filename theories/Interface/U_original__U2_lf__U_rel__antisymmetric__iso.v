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

#[export] Instance: MustUnfold (@Original.LF.Rel.antisymmetric) := {}.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf__U_rel__relation__iso.Interface <+ Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface.

Module Type Interface (Import args : Args).

Definition imported_Original_LF_Rel_antisymmetric : forall x : Type, (x -> x -> SProp) -> SProp
  := fun (x : Type) (x0 : x -> x -> SProp) => forall a' a'0 : x, x0 a' a'0 -> x0 a'0 a' -> imported_Corelib_Init_Logic_eq a' a'0.
Definition Original_LF_Rel_antisymmetric_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF.Rel.relation x1) (x4 : x2 -> x2 -> SProp),
  (forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (x3 x5 x7) (x4 x6 x8)) ->
  Iso (Original.LF.Rel.antisymmetric x3) (imported_Original_LF_Rel_antisymmetric x4)
  := fun (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF.Rel.relation x1) (x4 : x2 -> x2 -> SProp)
    (hx0 : forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (x3 x5 x7) (x4 x6 x8)) =>
  IsoForall (fun a : x1 => forall b : x1, x3 a b -> x3 b a -> a = b) (fun x6 : x2 => forall a' : x2, x4 x6 a' -> x4 a' x6 -> imported_Corelib_Init_Logic_eq x6 a')
    (fun (x5 : x1) (x6 : x2) (hx1 : rel_iso hx x5 x6) =>
     IsoForall (fun a : x1 => x3 x5 a -> x3 a x5 -> x5 = a) (fun x8 : x2 => x4 x6 x8 -> x4 x8 x6 -> imported_Corelib_Init_Logic_eq x6 x8)
       (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) => IsoArrow (hx0 x5 x6 hx1 x7 x8 hx2) (IsoArrow (hx0 x7 x8 hx2 x5 x6 hx1) (Corelib_Init_Logic_eq_iso hx1 hx2)))).
Existing Instance Original_LF_Rel_antisymmetric_iso.
#[export] Hint Extern 0 (IsoStatementProofFor (@Original.LF.Rel.antisymmetric) ?x) => unify x Original_LF_Rel_antisymmetric_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween (@Original.LF.Rel.antisymmetric) imported_Original_LF_Rel_antisymmetric ?x) => unify x Original_LF_Rel_antisymmetric_iso; constructor : typeclass_instances.


End Interface.