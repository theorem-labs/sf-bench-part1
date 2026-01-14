From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_false__iso Interface.U_logic__not__iso Interface.ex__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_false__iso Interface.U_logic__not__iso Interface.ex__iso.

  Export Interface.U_false__iso.CodeBlocks Interface.U_logic__not__iso.CodeBlocks Interface.ex__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_false__iso.Interface <+ Interface.U_logic__not__iso.Interface <+ Interface.ex__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_dist__not__exists : forall (x : Type) (x0 : x -> SProp), (forall x1 : x, x0 x1) -> imported_ex (fun H : x => x0 H -> imported_False) -> imported_False.
Parameter Original_LF__DOT__Logic_LF_Logic_dist__not__exists_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : x1 -> Prop) (x4 : x2 -> SProp) (hx0 : forall (x5 : x1) (x6 : x2), rel_iso hx x5 x6 -> Iso (x3 x5) (x4 x6)) (x5 : forall x : x1, x3 x)
    (x6 : forall x : x2, x4 x),
  (forall (x7 : x1) (x8 : x2) (hx1 : rel_iso hx x7 x8), rel_iso (hx0 x7 x8 hx1) (x5 x7) (x6 x8)) ->
  forall (x7 : exists x : x1, x3 x -> False) (x8 : imported_ex (fun H : x2 => x4 H -> imported_False)),
  rel_iso
    {|
      to := ex_iso (fun x : x1 => x3 x -> False) (fun H : x2 => x4 H -> imported_False) (fun (x9 : x1) (x10 : x2) (hx2 : rel_iso hx x9 x10) => IsoArrow (hx0 x9 x10 hx2) False_iso);
      from := from (ex_iso (fun x : x1 => x3 x -> False) (fun H : x2 => x4 H -> imported_False) (fun (x9 : x1) (x10 : x2) (hx2 : rel_iso hx x9 x10) => IsoArrow (hx0 x9 x10 hx2) False_iso));
      to_from :=
        fun x : imported_ex (fun H : x2 => x4 H -> imported_False) =>
        to_from (ex_iso (fun x0 : x1 => x3 x0 -> False) (fun H : x2 => x4 H -> imported_False) (fun (x9 : x1) (x10 : x2) (hx2 : rel_iso hx x9 x10) => IsoArrow (hx0 x9 x10 hx2) False_iso)) x;
      from_to :=
        fun x : exists y : x1, x3 y -> False =>
        seq_p_of_t
          (from_to (ex_iso (fun x0 : x1 => x3 x0 -> False) (fun H : x2 => x4 H -> imported_False) (fun (x9 : x1) (x10 : x2) (hx2 : rel_iso hx x9 x10) => IsoArrow (hx0 x9 x10 hx2) False_iso)) x)
    |} x7 x8 ->
  rel_iso {| to := False_iso; from := from False_iso; to_from := fun x : imported_False => to_from False_iso x; from_to := fun x : False => seq_p_of_t (from_to False_iso x) |}
    (Original.LF_DOT_Logic.LF.Logic.dist_not_exists x1 x3 x5 x7) (imported_Original_LF__DOT__Logic_LF_Logic_dist__not__exists x4 x6 x8).
Existing Instance Original_LF__DOT__Logic_LF_Logic_dist__not__exists_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.dist_not_exists ?x) => unify x Original_LF__DOT__Logic_LF_Logic_dist__not__exists_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.dist_not_exists imported_Original_LF__DOT__Logic_LF_Logic_dist__not__exists ?x) => unify x Original_LF__DOT__Logic_LF_Logic_dist__not__exists_iso; constructor : typeclass_instances.


End Interface.