From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.ex__iso Interface.nat__iso Interface.U_nat__add__iso Interface.U_s__iso Interface.__0__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_true__iso Interface.U_corelib__U_init__U_logic__eq__iso Interface.ex__iso Interface.nat__iso Interface.U_nat__add__iso Interface.U_s__iso Interface.__0__iso.

  Export Interface.U_true__iso.CodeBlocks Interface.U_corelib__U_init__U_logic__eq__iso.CodeBlocks Interface.ex__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_nat__add__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_true__iso.Interface <+ Interface.U_corelib__U_init__U_logic__eq__iso.Interface <+ Interface.ex__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_nat__add__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Logic_LF_Logic_exists__example__2 : forall x : imported_nat,
  imported_ex (fun H : imported_nat => imported_Corelib_Init_Logic_eq x (imported_Nat_add (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) H)) ->
  imported_ex (fun H : imported_nat => imported_Corelib_Init_Logic_eq x (imported_Nat_add (imported_S (imported_S imported_0)) H)).
Parameter Original_LF__DOT__Logic_LF_Logic_exists__example__2_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : exists m : nat, x1 = 4 + m)
    (x4 : imported_ex (fun H : imported_nat => imported_Corelib_Init_Logic_eq x2 (imported_Nat_add (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) H))),
  rel_iso
    {|
      to :=
        ex_iso (fun m : nat => x1 = 4 + m) (fun H : imported_nat => imported_Corelib_Init_Logic_eq x2 (imported_Nat_add (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) H))
          (fun (x5 : nat) (x6 : imported_nat) (hx0 : rel_iso nat_iso x5 x6) =>
           Corelib_Init_Logic_eq_iso hx (Nat_add_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso)))) hx0));
      from :=
        from
          (ex_iso (fun m : nat => x1 = 4 + m)
             (fun H : imported_nat => imported_Corelib_Init_Logic_eq x2 (imported_Nat_add (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) H))
             (fun (x5 : nat) (x6 : imported_nat) (hx0 : rel_iso nat_iso x5 x6) =>
              Corelib_Init_Logic_eq_iso hx (Nat_add_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso)))) hx0)));
      to_from :=
        fun x : imported_ex (fun H : imported_nat => imported_Corelib_Init_Logic_eq x2 (imported_Nat_add (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) H)) =>
        to_from
          (ex_iso (fun m : nat => x1 = 4 + m)
             (fun H : imported_nat => imported_Corelib_Init_Logic_eq x2 (imported_Nat_add (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) H))
             (fun (x5 : nat) (x6 : imported_nat) (hx0 : rel_iso nat_iso x5 x6) =>
              Corelib_Init_Logic_eq_iso hx (Nat_add_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso)))) hx0)))
          x;
      from_to :=
        fun x : exists y : nat, x1 = 4 + y =>
        seq_p_of_t
          (from_to
             (ex_iso (fun m : nat => x1 = 4 + m)
                (fun H : imported_nat => imported_Corelib_Init_Logic_eq x2 (imported_Nat_add (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0)))) H))
                (fun (x5 : nat) (x6 : imported_nat) (hx0 : rel_iso nat_iso x5 x6) =>
                 Corelib_Init_Logic_eq_iso hx (Nat_add_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 0 imported_0 _0_iso)))) hx0)))
             x)
    |} x3 x4 ->
  rel_iso
    {|
      to :=
        ex_iso (fun o : nat => x1 = 2 + o) (fun H : imported_nat => imported_Corelib_Init_Logic_eq x2 (imported_Nat_add (imported_S (imported_S imported_0)) H))
          (fun (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6) => Corelib_Init_Logic_eq_iso hx (Nat_add_iso (S_iso (S_iso _0_iso)) hx1));
      from :=
        from
          (ex_iso (fun o : nat => x1 = 2 + o) (fun H : imported_nat => imported_Corelib_Init_Logic_eq x2 (imported_Nat_add (imported_S (imported_S imported_0)) H))
             (fun (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6) => Corelib_Init_Logic_eq_iso hx (Nat_add_iso (S_iso (S_iso _0_iso)) hx1)));
      to_from :=
        fun x : imported_ex (fun H : imported_nat => imported_Corelib_Init_Logic_eq x2 (imported_Nat_add (imported_S (imported_S imported_0)) H)) =>
        to_from
          (ex_iso (fun o : nat => x1 = 2 + o) (fun H : imported_nat => imported_Corelib_Init_Logic_eq x2 (imported_Nat_add (imported_S (imported_S imported_0)) H))
             (fun (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6) => Corelib_Init_Logic_eq_iso hx (Nat_add_iso (S_iso (S_iso _0_iso)) hx1)))
          x;
      from_to :=
        fun x : exists y : nat, x1 = 2 + y =>
        seq_p_of_t
          (from_to
             (ex_iso (fun o : nat => x1 = 2 + o) (fun H : imported_nat => imported_Corelib_Init_Logic_eq x2 (imported_Nat_add (imported_S (imported_S imported_0)) H))
                (fun (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6) => Corelib_Init_Logic_eq_iso hx (Nat_add_iso (S_iso (S_iso _0_iso)) hx1)))
             x)
    |} (Original.LF_DOT_Logic.LF.Logic.exists_example_2 x1 x3) (imported_Original_LF__DOT__Logic_LF_Logic_exists__example__2 x4).
Existing Instance Original_LF__DOT__Logic_LF_Logic_exists__example__2_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.exists_example_2 ?x) => unify x Original_LF__DOT__Logic_LF_Logic_exists__example__2_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.exists_example_2 imported_Original_LF__DOT__Logic_LF_Logic_exists__example__2 ?x) => unify x Original_LF__DOT__Logic_LF_Logic_exists__example__2_iso; constructor : typeclass_instances.


End Interface.