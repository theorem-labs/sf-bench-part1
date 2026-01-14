From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf__U_rel__relation__iso Interface.U_original__U2_lf__U_rel__clos____refl____trans____1n__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf__U_rel__relation__iso Interface.U_original__U2_lf__U_rel__clos____refl____trans____1n__iso.

  Export Interface.U_original__U2_lf__U_rel__relation__iso.CodeBlocks Interface.U_original__U2_lf__U_rel__clos____refl____trans____1n__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf__U_rel__relation__iso.Interface <+ Interface.U_original__U2_lf__U_rel__clos____refl____trans____1n__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF_Rel_rsc__R : forall (x : Type) (x0 : x -> x -> SProp) (x1 x2 : x), x0 x1 x2 -> imported_Original_LF_Rel_clos__refl__trans__1n (fun x3 x4 : x => x0 x3 x4) x1 x2.
Parameter Original_LF_Rel_rsc__R_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF.Rel.relation x1) (x4 : x2 -> x2 -> SProp)
    (hx0 : forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (x3 x5 x7) (x4 x6 x8)) (x5 : x1) (x6 : x2) (hx1 : rel_iso hx x5 x6) 
    (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) (x9 : x3 x5 x7) (x10 : x4 x6 x8),
  rel_iso (hx0 x5 x6 hx1 x7 x8 hx2) x9 x10 ->
  rel_iso
    (Original_LF_Rel_clos__refl__trans__1n_iso x3 (fun x x0 : x2 => x4 x x0)
       (fun (x11 : x1) (x12 : x2) (hx4 : rel_iso hx x11 x12) (x13 : x1) (x14 : x2) (hx5 : rel_iso hx x13 x14) => hx0 x11 x12 hx4 x13 x14 hx5) hx1 hx2)
    (Original.LF.Rel.rsc_R x1 x3 x5 x7 x9) (imported_Original_LF_Rel_rsc__R x4 x6 x8 x10).
Existing Instance Original_LF_Rel_rsc__R_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF.Rel.rsc_R ?x) => unify x Original_LF_Rel_rsc__R_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF.Rel.rsc_R imported_Original_LF_Rel_rsc__R ?x) => unify x Original_LF_Rel_rsc__R_iso; constructor : typeclass_instances.


End Interface.