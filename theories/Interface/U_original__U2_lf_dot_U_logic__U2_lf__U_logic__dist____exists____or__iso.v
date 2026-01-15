From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.ex__iso Interface.iff__iso Interface.or__iso.

Module Export CodeBlocks.

  Export (hints) Interface.ex__iso Interface.iff__iso Interface.or__iso.

  Export Interface.ex__iso.CodeBlocks Interface.iff__iso.CodeBlocks Interface.or__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.ex__iso.Interface <+ Interface.iff__iso.Interface <+ Interface.or__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_dist__exists__or : forall (x : Type) (x0 x1 : x -> SProp), imported_iff (imported_ex (fun H : x => imported_or (x0 H) (x1 H))) (imported_or (imported_ex (fun H : x => x0 H)) (imported_ex (fun H : x => x1 H))).
Parameter Original_LF__DOT__Logic_LF_Logic_dist__exists__or_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1 -> Prop) (x4 : x2 -> SProp) (hx0 : forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 x5) (x4 x6)) (x5 : x1 -> Prop) 
    (x6 : x2 -> SProp) (hx1 : forall (x7 : x1) (x8 : x2), rel_iso hx x7 x8 -> Iso (x5 x7) (x6 x8)),
  rel_iso
    (relax_Iso_Ts_Ps
       (iff_iso (ex_iso (fun x : x1 => x3 x \/ x5 x) (fun H : x2 => imported_or (x4 H) (x6 H)) (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) => or_iso (hx0 x7 x8 hx2) (hx1 x7 x8 hx2)))
          (or_iso (ex_iso (fun x : x1 => x3 x) (fun H : x2 => x4 H) (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) => hx0 x7 x8 hx2))
             (ex_iso (fun x : x1 => x5 x) (fun H : x2 => x6 H) (fun (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8) => hx1 x7 x8 hx2)))))
    (Original.LF_DOT_Logic.LF.Logic.dist_exists_or x1 x3 x5) (imported_Original_LF__DOT__Logic_LF_Logic_dist__exists__or x4 x6).
Existing Instance Original_LF__DOT__Logic_LF_Logic_dist__exists__or_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.dist_exists_or ?x) => unify x Original_LF__DOT__Logic_LF_Logic_dist__exists__or_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.dist_exists_or imported_Original_LF__DOT__Logic_LF_Logic_dist__exists__or ?x) => unify x Original_LF__DOT__Logic_LF_Logic_dist__exists__or_iso; constructor : typeclass_instances.


End Interface.