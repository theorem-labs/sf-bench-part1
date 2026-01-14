From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export 
  Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__list__iso
  Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__app__iso
  Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso
  Isomorphisms.iff__iso
  Isomorphisms.or__iso.

(* The imported In_app_iff axiom *)
Definition imported_Original_LF__DOT__Logic_LF_Logic_In__app__iff : forall (x : Type) (x0 x1 : imported_Original_LF__DOT__Poly_LF_Poly_list x) (x2 : x),
  imported_iff (imported_Original_LF__DOT__Logic_LF_Logic_In x2 (imported_Original_LF__DOT__Poly_LF_Poly_app x0 x1))
    (imported_or (imported_Original_LF__DOT__Logic_LF_Logic_In x2 x0) (imported_Original_LF__DOT__Logic_LF_Logic_In x2 x1)) :=
  Imported.Original_LF__DOT__Logic_LF_Logic_In__app__iff.

(* The isomorphism - this is an axiom-to-axiom mapping, so we can admit it *)
Instance Original_LF__DOT__Logic_LF_Logic_In__app__iff_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Poly.LF.Poly.list x1) (x4 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
    (hx0 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x3 x4) (x5 : Original.LF_DOT_Poly.LF.Poly.list x1) (x6 : imported_Original_LF__DOT__Poly_LF_Poly_list x2)
    (hx1 : rel_iso (Original_LF__DOT__Poly_LF_Poly_list_iso hx) x5 x6) (x7 : x1) (x8 : x2) (hx2 : rel_iso hx x7 x8),
  rel_iso
    {|
      to :=
        iff_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 (Original_LF__DOT__Poly_LF_Poly_app_iso hx0 hx1))
          (or_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 hx0) (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 hx1));
      from :=
        from
          (iff_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 (Original_LF__DOT__Poly_LF_Poly_app_iso hx0 hx1))
             (or_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 hx0) (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 hx1)));
      to_from :=
        fun
          x : imported_iff (imported_Original_LF__DOT__Logic_LF_Logic_In x8 (imported_Original_LF__DOT__Poly_LF_Poly_app x4 x6))
                (imported_or (imported_Original_LF__DOT__Logic_LF_Logic_In x8 x4) (imported_Original_LF__DOT__Logic_LF_Logic_In x8 x6)) =>
        to_from
          (iff_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 (Original_LF__DOT__Poly_LF_Poly_app_iso hx0 hx1))
             (or_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 hx0) (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 hx1)))
          x;
      from_to :=
        fun x : Original.LF_DOT_Logic.LF.Logic.In x7 (Original.LF_DOT_Poly.LF.Poly.app x3 x5) <-> Original.LF_DOT_Logic.LF.Logic.In x7 x3 \/ Original.LF_DOT_Logic.LF.Logic.In x7 x5 =>
        seq_p_of_t
          (from_to
             (iff_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 (Original_LF__DOT__Poly_LF_Poly_app_iso hx0 hx1))
                (or_iso (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 hx0) (Original_LF__DOT__Logic_LF_Logic_In_iso hx2 hx1)))
             x)
    |} (Original.LF_DOT_Logic.LF.Logic.In_app_iff x1 x3 x5 x7) (imported_Original_LF__DOT__Logic_LF_Logic_In__app__iff x4 x6 x8).
Proof.
  intros.
  unfold rel_iso.
  (* The result type of this rel_iso is an SProp since it's in the imported_iff type.
     So we can just prove eq_refl. *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.In_app_iff := {}. 
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_In__app__iff := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.In_app_iff Original_LF__DOT__Logic_LF_Logic_In__app__iff_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.In_app_iff Imported.Original_LF__DOT__Logic_LF_Logic_In__app__iff Original_LF__DOT__Logic_LF_Logic_In__app__iff_iso := {}.
