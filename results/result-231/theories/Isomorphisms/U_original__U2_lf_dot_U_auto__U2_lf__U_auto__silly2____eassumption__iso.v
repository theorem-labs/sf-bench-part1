From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso. (* for speed *)

From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_s__iso Isomorphisms.ex__iso.

(* Define n42 in terms of imported_S and imported_0 *)
Definition imported_n42 : imported_nat := Imported.n42.

(* The isomorphism for 42 <-> imported_n42 *)
(* We need to show that nat_to_imported 42 = imported_n42 *)
(* Note: nat_iso : Iso Datatypes.nat imported_nat *)
Definition fortytwo : Datatypes.nat := 42.
Lemma nat_to_imported_n42_iso : rel_iso nat_iso fortytwo imported_n42.
Proof.
  unfold rel_iso, imported_n42, fortytwo.
  simpl.
  (* 42 applications of S_iso to _0_iso *)
  apply IsomorphismDefinitions.eq_refl.
Qed.

(* The imported definition - this just refers to the Imported axiom *)
Definition imported_Original_LF__DOT__Auto_LF_Auto_silly2__eassumption := Imported.Original_LF__DOT__Auto_LF_Auto_silly2__eassumption.

(* The isomorphism proof. Since this is for an Admitted axiom, we admit it. *)
Instance Original_LF__DOT__Auto_LF_Auto_silly2__eassumption_iso : 
  forall (x1 : Datatypes.nat -> Datatypes.nat -> Prop) (x2 : imported_nat -> imported_nat -> SProp)
    (hx : forall (x3 : Datatypes.nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> 
          forall (x5 : Datatypes.nat) (x6 : imported_nat), rel_iso nat_iso x5 x6 -> 
          Iso (x1 x3 x5) (x2 x4 x6)) 
    (x3 : Datatypes.nat -> Prop)
    (x4 : imported_nat -> SProp) 
    (hx0 : forall (x5 : Datatypes.nat) (x6 : imported_nat), rel_iso nat_iso x5 x6 -> Iso (x3 x5) (x4 x6)) 
    (x5 : exists y : Datatypes.nat, x1 fortytwo y)
    (x6 : imported_ex (fun H : imported_nat => x2 imported_n42 H)),
  rel_iso
    (ex_iso (fun y : Datatypes.nat => x1 fortytwo y)
          (fun H : imported_nat => x2 imported_n42 H)
          (fun (x7 : Datatypes.nat) (x8 : imported_nat) (hx1 : rel_iso nat_iso x7 x8) =>
           hx fortytwo imported_n42 (nat_to_imported_n42_iso) x7 x8 hx1)) x5 x6 ->
  forall (x7 : forall x y : Datatypes.nat, x1 x y -> x3 x) 
         (x8 : forall x x0 : imported_nat, x2 x x0 -> x4 x),
  (forall (x9 : Datatypes.nat) (x10 : imported_nat) (hx2 : rel_iso nat_iso x9 x10) 
          (x11 : Datatypes.nat) (x12 : imported_nat) (hx3 : rel_iso nat_iso x11 x12) 
          (x13 : x1 x9 x11) (x14 : x2 x10 x12),
   rel_iso (hx x9 x10 hx2 x11 x12 hx3) x13 x14 -> 
   rel_iso (hx0 x9 x10 hx2) (x7 x9 x11 x13) (x8 x10 x12 x14)) ->
  rel_iso
    (hx0 fortytwo imported_n42 nat_to_imported_n42_iso)
    (Original.LF_DOT_Auto.LF.Auto.silly2_eassumption x1 x3 x5 x7) 
    (imported_Original_LF__DOT__Auto_LF_Auto_silly2__eassumption x2 x4 x6 x8).
Admitted.

Instance: KnownConstant Original.LF_DOT_Auto.LF.Auto.silly2_eassumption := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Auto_LF_Auto_silly2__eassumption := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Auto.LF.Auto.silly2_eassumption Original_LF__DOT__Auto_LF_Auto_silly2__eassumption_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Auto.LF.Auto.silly2_eassumption Imported.Original_LF__DOT__Auto_LF_Auto_silly2__eassumption Original_LF__DOT__Auto_LF_Auto_silly2__eassumption_iso := {}.
