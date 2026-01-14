From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.cons__iso Isomorphisms.nil__iso Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_AExp_invert__example1 : forall x x0 x1 : imported_nat,
  imported_Corelib_Init_Logic_eq (imported_cons x (imported_cons x0 (imported_nil imported_nat))) (imported_cons x (imported_cons x1 (imported_nil imported_nat))) ->
  imported_Corelib_Init_Logic_eq x0 x1 := (@Imported.Original_LF__DOT__Imp_LF_Imp_AExp_invert__example1).
Instance Original_LF__DOT__Imp_LF_Imp_AExp_invert__example1_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2) (x3 : nat) (x4 : imported_nat) (hx0 : rel_iso nat_iso x3 x4) (x5 : nat) (x6 : imported_nat) (hx1 : rel_iso nat_iso x5 x6)
    (x7 : (x1 :: x3 :: nil)%list = (x1 :: x5 :: nil)%list)
    (x8 : imported_Corelib_Init_Logic_eq (imported_cons x2 (imported_cons x4 (imported_nil imported_nat))) (imported_cons x2 (imported_cons x6 (imported_nil imported_nat)))),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (cons_iso hx (cons_iso hx0 (nil_iso nat_iso))) (cons_iso hx (cons_iso hx1 (nil_iso nat_iso)));
      from := from (Corelib_Init_Logic_eq_iso (cons_iso hx (cons_iso hx0 (nil_iso nat_iso))) (cons_iso hx (cons_iso hx1 (nil_iso nat_iso))));
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_cons x2 (imported_cons x4 (imported_nil imported_nat))) (imported_cons x2 (imported_cons x6 (imported_nil imported_nat))) =>
        to_from (Corelib_Init_Logic_eq_iso (cons_iso hx (cons_iso hx0 (nil_iso nat_iso))) (cons_iso hx (cons_iso hx1 (nil_iso nat_iso)))) x;
      from_to :=
        fun x : (x1 :: x3 :: nil)%list = (x1 :: x5 :: nil)%list =>
        seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (cons_iso hx (cons_iso hx0 (nil_iso nat_iso))) (cons_iso hx (cons_iso hx1 (nil_iso nat_iso)))) x)
    |} x7 x8 ->
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso hx0 hx1;
      from := from (Corelib_Init_Logic_eq_iso hx0 hx1);
      to_from := fun x : imported_Corelib_Init_Logic_eq x4 x6 => to_from (Corelib_Init_Logic_eq_iso hx0 hx1) x;
      from_to := fun x : x3 = x5 => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso hx0 hx1) x)
    |} (Original.LF_DOT_Imp.LF.Imp.AExp.invert_example1 x7) (imported_Original_LF__DOT__Imp_LF_Imp_AExp_invert__example1 x8).
Proof.
  intros x1 x2 hx x3 x4 hx0 x5 x6 hx1 x7 x8 Hrel_input.
  (* The goal is an SProp equality between two SProp proofs.
     Both sides produce proofs of imported_Corelib_Init_Logic_eq x4 x6.
     Since this is in SProp, all proofs are equal by definitional UIP. *)
  unfold rel_iso.
  simpl.
  (* Need to show: to (Corelib_Init_Logic_eq_iso hx0 hx1) (Original.LF_DOT_Imp.LF.Imp.AExp.invert_example1 x7) 
                   = imported_Original_LF__DOT__Imp_LF_Imp_AExp_invert__example1 x8 *)
  (* Both are proofs in SProp, so they are definitionally equal *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant (@Original.LF_DOT_Imp.LF.Imp.AExp.invert_example1) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant (@Imported.Original_LF__DOT__Imp_LF_Imp_AExp_invert__example1) := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor (@Original.LF_DOT_Imp.LF.Imp.AExp.invert_example1) Original_LF__DOT__Imp_LF_Imp_AExp_invert__example1_iso := {}.
Instance: IsoStatementProofBetween (@Original.LF_DOT_Imp.LF.Imp.AExp.invert_example1) (@Imported.Original_LF__DOT__Imp_LF_Imp_AExp_invert__example1) Original_LF__DOT__Imp_LF_Imp_AExp_invert__example1_iso := {}.