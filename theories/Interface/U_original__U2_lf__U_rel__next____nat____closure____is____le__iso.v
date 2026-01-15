From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_original__U2_lf__U_rel__relation__iso Interface.U_original__U2_lf__U_rel__clos____refl____trans__iso Interface.iff__iso Interface.nat__iso Interface.U_original__U2_lf__U_rel__next____nat__iso Interface.le__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_original__U2_lf__U_rel__relation__iso Interface.U_original__U2_lf__U_rel__clos____refl____trans__iso Interface.iff__iso Interface.nat__iso Interface.U_original__U2_lf__U_rel__next____nat__iso Interface.le__iso.

  Export Interface.U_original__U2_lf__U_rel__relation__iso.CodeBlocks Interface.U_original__U2_lf__U_rel__clos____refl____trans__iso.CodeBlocks Interface.iff__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf__U_rel__next____nat__iso.CodeBlocks Interface.le__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_original__U2_lf__U_rel__relation__iso.Interface <+ Interface.U_original__U2_lf__U_rel__clos____refl____trans__iso.Interface <+ Interface.iff__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf__U_rel__next____nat__iso.Interface <+ Interface.le__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF_Rel_next__nat__closure__is__le : forall x x0 : imported_nat, imported_iff (imported_le x x0) (imported_Original_LF_Rel_clos__refl__trans (fun H H0 : imported_nat => imported_Original_LF_Rel_next__nat H H0) x x0).
Parameter Original_LF_Rel_next__nat__closure__is__le_iso : forall (x1 : nat) (x2 : imported_nat) (hx : @rel_iso nat imported_nat nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : @rel_iso nat imported_nat nat_iso x3 x4),
  @rel_iso (x1 <= x3 <-> @Original.LF.Rel.clos_refl_trans nat Original.LF.Rel.next_nat x1 x3)
    (imported_iff (imported_le x2 x4) (@imported_Original_LF_Rel_clos__refl__trans imported_nat (fun H H0 : imported_nat => imported_Original_LF_Rel_next__nat H H0) x2 x4))
    (@relax_Iso_Ts_Ps (x1 <= x3 <-> @Original.LF.Rel.clos_refl_trans nat Original.LF.Rel.next_nat x1 x3)
       (imported_iff (imported_le x2 x4) (@imported_Original_LF_Rel_clos__refl__trans imported_nat (fun H H0 : imported_nat => imported_Original_LF_Rel_next__nat H H0) x2 x4))
       (@iff_iso (x1 <= x3) (imported_le x2 x4) (@le_iso x1 x2 hx x3 x4 hx0) (@Original.LF.Rel.clos_refl_trans nat Original.LF.Rel.next_nat x1 x3)
          (@imported_Original_LF_Rel_clos__refl__trans imported_nat (fun H H0 : imported_nat => imported_Original_LF_Rel_next__nat H H0) x2 x4)
          (@Original_LF_Rel_clos__refl__trans_iso nat imported_nat nat_iso Original.LF.Rel.next_nat (fun H H0 : imported_nat => imported_Original_LF_Rel_next__nat H H0)
             (fun (x5 : nat) (x6 : imported_nat) (hx1 : @rel_iso nat imported_nat nat_iso x5 x6) (x7 : nat) (x8 : imported_nat) (hx2 : @rel_iso nat imported_nat nat_iso x7 x8) =>
              @Original_LF_Rel_next__nat_iso x5 x6 hx1 x7 x8 hx2)
             x1 x2 hx x3 x4 hx0)))
    (Original.LF.Rel.next_nat_closure_is_le x1 x3) (imported_Original_LF_Rel_next__nat__closure__is__le x2 x4).
Existing Instance Original_LF_Rel_next__nat__closure__is__le_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF.Rel.next_nat_closure_is_le ?x) => unify x Original_LF_Rel_next__nat__closure__is__le_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF.Rel.next_nat_closure_is_le imported_Original_LF_Rel_next__nat__closure__is__le ?x) => unify x Original_LF_Rel_next__nat__closure__is__le_iso; constructor : typeclass_instances.


End Interface.