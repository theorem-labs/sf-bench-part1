From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_poly__U2_lf__U_poly__doit3times__iso Isomorphisms.__0__iso Isomorphisms.U_nat__mul__iso Isomorphisms.U_s__iso.

(* Imported.nat_2 = imported_S (imported_S imported_0) by reflexivity *)
(* We need to show that Imported.nat_256 = imported_S (imported_S (imported_S (iterate1 imported_S 253 imported_0))) *)

Lemma nat_256_eq : Imported.nat_256 = imported_S (imported_S (imported_S (iterate1 imported_S 253 imported_0))).
Proof.
  vm_compute. reflexivity.
Qed.

Lemma nat_2_eq : Imported.nat_2 = imported_S (imported_S imported_0).
Proof.
  reflexivity.
Qed.

(* The imported definition using Imported.nat_2 and Imported.nat_256 is convertible to the required form *)
Definition imported_Original_LF__DOT__Poly_LF_Poly_test__anon__fun' : imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Poly_LF_Poly_doit3times (fun x : imported_nat => imported_Nat_mul x x) (imported_S (imported_S imported_0)))
    (imported_S (imported_S (imported_S (iterate1 imported_S 253 imported_0)))).
Proof.
  (* The type of Imported.Original_LF__DOT__Poly_LF_Poly_test__anon__fun' is 
     Imported.Corelib_Init_Logic_eq Imported.nat
       (Imported.Original_LF__DOT__Poly_LF_Poly_doit3times Imported.nat
          (fun x : Imported.nat => Imported.Nat_mul x x) Imported.nat_2)
       Imported.nat_256
     which is convertible to our goal *)
  exact Imported.Original_LF__DOT__Poly_LF_Poly_test__anon__fun'.
Defined.

Instance Original_LF__DOT__Poly_LF_Poly_test__anon__fun'_iso : rel_iso
    (relax_Iso_Ts_Ps
       (Corelib_Init_Logic_eq_iso
          (unwrap_sprop
             (Original_LF__DOT__Poly_LF_Poly_doit3times_iso (IsoIso nat_iso) (fun n : nat => n * n) (fun x : imported_nat => imported_Nat_mul x x)
                (fun (x1 : nat) (x2 : imported_nat) (hx : rel_iso_sort (IsoIso nat_iso) x1 x2) => {| unwrap_sprop := Nat_mul_iso (unwrap_sprop hx) (unwrap_sprop hx) |}) (S (S O))
                (imported_S (imported_S imported_0)) {| unwrap_sprop := S_iso (S_iso _0_iso) |}))
          (S_iso (S_iso (S_iso (iterate1D2 S imported_S S_iso 253 O imported_0 _0_iso))))))
    Original.LF_DOT_Poly.LF.Poly.test_anon_fun' imported_Original_LF__DOT__Poly_LF_Poly_test__anon__fun'.
Proof.
  (* Both sides are in SProp, so we use proof irrelevance *)
  unfold rel_iso. simpl.
  (* The goal is now: eq (to ... Original.test_anon_fun') imported_... *)
  (* Both are SProp equality proofs, so they are equal by SProp proof irrelevance *)
  apply IsomorphismDefinitions.eq_refl.
Defined.
Instance: KnownConstant Original.LF_DOT_Poly.LF.Poly.test_anon_fun' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Poly_LF_Poly_test__anon__fun' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Poly.LF.Poly.test_anon_fun' Original_LF__DOT__Poly_LF_Poly_test__anon__fun'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Poly.LF.Poly.test_anon_fun' Imported.Original_LF__DOT__Poly_LF_Poly_test__anon__fun' Original_LF__DOT__Poly_LF_Poly_test__anon__fun'_iso := {}.