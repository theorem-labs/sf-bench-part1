From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.__0__iso Isomorphisms.U_nat__mul__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_mult__0__l : forall x : imported_nat, imported_Corelib_Init_Logic_eq (imported_Nat_mul imported_0 x) imported_0 := Imported.Original_LF__DOT__Basics_LF_Basics_mult__0__l.
Instance Original_LF__DOT__Basics_LF_Basics_mult__0__l_iso : forall (x1 : Datatypes.nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Nat_mul_iso _0_iso hx) _0_iso;
      from := from (Corelib_Init_Logic_eq_iso (Nat_mul_iso _0_iso hx) _0_iso);
      to_from := fun x : imported_Corelib_Init_Logic_eq (imported_Nat_mul imported_0 x2) imported_0 => to_from (Corelib_Init_Logic_eq_iso (Nat_mul_iso _0_iso hx) _0_iso) x;
      from_to := fun x : Datatypes.O * x1 = Datatypes.O => seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Nat_mul_iso _0_iso hx) _0_iso) x)
    |} (Original.LF_DOT_Basics.LF.Basics.mult_0_l x1) (imported_Original_LF__DOT__Basics_LF_Basics_mult__0__l x2).
Proof.
  intros x1 x2 hx.
  (* The rel_iso for equality types is just reflexivity in SProp since both sides are equal *)
  unfold rel_iso. simpl.
  (* to (Corelib_Init_Logic_eq_iso ...) (mult_0_l x1) should equal imported_Original... x2 *)
  (* Since both proofs are of proposition types (equality), and SProp has proof irrelevance,
     we just need to show the types match, which they do by construction *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.mult_0_l := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_mult__0__l := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.mult_0_l Original_LF__DOT__Basics_LF_Basics_mult__0__l_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.mult_0_l Imported.Original_LF__DOT__Basics_LF_Basics_mult__0__l Original_LF__DOT__Basics_LF_Basics_mult__0__l_iso := {}.