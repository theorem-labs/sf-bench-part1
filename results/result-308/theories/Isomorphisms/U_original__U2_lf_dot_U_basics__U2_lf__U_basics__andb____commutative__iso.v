From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__andb__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_andb__commutative : forall x x0 : imported_Original_LF__DOT__Basics_LF_Basics_bool,
  imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_andb x x0) (imported_Original_LF__DOT__Basics_LF_Basics_andb x0 x) := Imported.Original_LF__DOT__Basics_LF_Basics_andb__commutative.
Instance Original_LF__DOT__Basics_LF_Basics_andb__commutative_iso : forall (x1 : Original.LF_DOT_Basics.LF.Basics.bool) (x2 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x1 x2)
    (x3 : Original.LF_DOT_Basics.LF.Basics.bool) (x4 : imported_Original_LF__DOT__Basics_LF_Basics_bool) (hx0 : rel_iso Original_LF__DOT__Basics_LF_Basics_bool_iso x3 x4),
  rel_iso
    {|
      to := Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_andb_iso hx hx0) (Original_LF__DOT__Basics_LF_Basics_andb_iso hx0 hx);
      from := from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_andb_iso hx hx0) (Original_LF__DOT__Basics_LF_Basics_andb_iso hx0 hx));
      to_from :=
        fun x : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_andb x2 x4) (imported_Original_LF__DOT__Basics_LF_Basics_andb x4 x2) =>
        to_from (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_andb_iso hx hx0) (Original_LF__DOT__Basics_LF_Basics_andb_iso hx0 hx)) x;
      from_to :=
        fun x : Original.LF_DOT_Basics.LF.Basics.andb x1 x3 = Original.LF_DOT_Basics.LF.Basics.andb x3 x1 =>
        seq_p_of_t (from_to (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_andb_iso hx hx0) (Original_LF__DOT__Basics_LF_Basics_andb_iso hx0 hx)) x)
    |} (Original.LF_DOT_Basics.LF.Basics.andb_commutative x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_andb__commutative x2 x4).
Proof.
  intros x1 x2 hx x3 x4 hx0.
  unfold rel_iso. simpl.
  (* The goal is to show that the 'to' of the Iso applied to Original's andb_commutative
     equals the Imported version. Since both are in SProp, any two proofs are equal. *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.andb_commutative := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_andb__commutative := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.andb_commutative Original_LF__DOT__Basics_LF_Basics_andb__commutative_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.andb_commutative Imported.Original_LF__DOT__Basics_LF_Basics_andb__commutative Original_LF__DOT__Basics_LF_Basics_andb__commutative_iso := {}.