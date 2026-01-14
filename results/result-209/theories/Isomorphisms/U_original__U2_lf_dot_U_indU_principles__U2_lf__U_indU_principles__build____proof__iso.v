From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.__0__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof : forall x : imported_nat -> SProp, x imported_0 -> (forall x0 : imported_nat, x x0 -> x (imported_S x0)) -> forall x2 : imported_nat, x x2 := Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof.

(* The main isomorphism proof *)
(* The key insight is:
   - rel_iso i a b = eq (to i a) b, which is an SProp
   - x2 x8 is an SProp (since x2 : imported_nat -> SProp)
   - In SProp, all inhabitants are definitionally equal: forall (A : SProp) (x y : A), eq x y
   - So we just need to show that both sides are in x2 x8, then eq_refl proves they're equal
*)
Instance Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof_iso : forall (x1 : Datatypes.nat -> Prop) (x2 : imported_nat -> SProp) (hx : forall (x3 : Datatypes.nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> Iso (x1 x3) (x2 x4)) (x3 : x1 O) (x4 : x2 imported_0),
  rel_iso (hx O imported_0 _0_iso) x3 x4 ->
  forall (x5 : forall n : Datatypes.nat, x1 n -> x1 (Datatypes.S n)) (x6 : forall x : imported_nat, x2 x -> x2 (imported_S x)),
  (forall (x7 : Datatypes.nat) (x8 : imported_nat) (hx1 : rel_iso nat_iso x7 x8) (x9 : x1 x7) (x10 : x2 x8),
   rel_iso (hx x7 x8 hx1) x9 x10 -> rel_iso (hx (Datatypes.S x7) (imported_S x8) (S_iso hx1)) (x5 x7 x9) (x6 x8 x10)) ->
  forall (x7 : Datatypes.nat) (x8 : imported_nat) (hx2 : rel_iso nat_iso x7 x8),
  rel_iso (hx x7 x8 hx2) (Original.LF_DOT_IndPrinciples.LF.IndPrinciples.build_proof x1 x3 x5 x7) (imported_Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof x2 x4 x6 x8).
Proof.
  intros x1 x2 hx x3 x4 Hbase x5 x6 Hstep.
  (* We prove by induction on x7 *)
  fix IH 1.
  intros x7 x8 hx2.
  destruct x7 as [|n'].
  - (* Base case: x7 = 0 *)
    simpl.
    unfold rel_iso.
    (* The goal is: IsomorphismDefinitions.eq (to (hx 0 x8 hx2) x3) (imported_..._build__proof x2 x4 x6 x8) *)
    (* Both sides are in x2 x8, which is an SProp, so they are equal by IsomorphismDefinitions.eq_refl *)
    (* In SProp, any two inhabitants are definitionally equal *)
    exact IsomorphismDefinitions.eq_refl.
  - (* Inductive case: x7 = S n' *)
    simpl.
    unfold rel_iso.
    (* The goal is: IsomorphismDefinitions.eq (to (hx (S n') x8 hx2) (x5 n' (build_proof x1 x3 x5 n'))) 
                       (imported_..._build__proof x2 x4 x6 x8) *)
    (* Both sides are in x2 x8, which is an SProp, so they are equal by IsomorphismDefinitions.eq_refl *)
    exact IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_IndPrinciples.LF.IndPrinciples.build_proof := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_IndPrinciples.LF.IndPrinciples.build_proof Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_IndPrinciples.LF.IndPrinciples.build_proof Imported.Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof Original_LF__DOT__IndPrinciples_LF_IndPrinciples_build__proof_iso := {}.