From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_in__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__cons__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__nil__iso Isomorphisms.__0__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Logic_LF_Logic_In__example__1 : imported_Original_LF__DOT__Logic_LF_Logic_In (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0))))
    (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S imported_0)
       (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S imported_0))
          (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S imported_0)))
             (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (iterate1 imported_S 1 imported_0))))
                (imported_Original_LF__DOT__Poly_LF_Poly_cons (imported_S (imported_S (imported_S (iterate1 imported_S 2 imported_0)))) (imported_Original_LF__DOT__Poly_LF_Poly_nil imported_nat)))))) := Imported.Original_LF__DOT__Logic_LF_Logic_In__example__1.
Instance Original_LF__DOT__Logic_LF_Logic_In__example__1_iso : rel_iso
    (Original_LF__DOT__Logic_LF_Logic_In_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 Datatypes.O imported_0 _0_iso))))
       (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso _0_iso)
          (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso _0_iso))
             (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso _0_iso)))
                (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 1 Datatypes.O imported_0 _0_iso))))
                   (Original_LF__DOT__Poly_LF_Poly_cons_iso (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 2 Datatypes.O imported_0 _0_iso)))) (Original_LF__DOT__Poly_LF_Poly_nil_iso nat_iso)))))))
    Original.LF_DOT_Logic.LF.Logic.In_example_1 imported_Original_LF__DOT__Logic_LF_Logic_In__example__1.
Proof.
  (* rel_iso for an Iso between Prop and SProp is: eq (to iso x) y
     Here x : Original.In ... (Prop) and y : Imported.In ... (SProp)
     to iso x : SProp, so we need eq (to iso x) y which is SProp equality.
     Since both sides are in SProp, and SProp has definitional UIP, this should be trivial. *)
  unfold rel_iso. simpl.
  (* The goal should be IsomorphismDefinitions.eq (to (...) Original.In_example_1) imported_In_example_1 *)
  (* Both are in SProp, so they are equal by proof irrelevance in SProp *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.In_example_1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_In__example__1 := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.In_example_1 Original_LF__DOT__Logic_LF_Logic_In__example__1_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.In_example_1 Imported.Original_LF__DOT__Logic_LF_Logic_In__example__1 Original_LF__DOT__Logic_LF_Logic_In__example__1_iso := {}.