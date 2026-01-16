From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
(* Typeclasses Opaque rel_iso. *) (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Nat_mul : imported_nat -> imported_nat -> imported_nat := Imported.Nat_mul.

(* First, we need to show that nat_to_imported respects multiplication *)
(* The Lean Nat_mul is defined with:
   Nat_mul O _ = O
   Nat_mul (S m) n = Nat_add (Nat_mul m n) n
   where Nat_add O n = n and Nat_add (S m) n = S (Nat_add m n)
*)

(* First prove addition compatibility *)
Fixpoint nat_add_compat (x y : Datatypes.nat) {struct x} :
  nat_to_imported (x + y) = Imported.Nat_add (nat_to_imported x) (nat_to_imported y) :=
  match x as x0 return nat_to_imported (x0 + y) = Imported.Nat_add (nat_to_imported x0) (nat_to_imported y) with
  | O => Logic.eq_refl
  | Datatypes.S x' => 
      match nat_add_compat x' y in (_ = z) return Imported.nat_S (nat_to_imported (x' + y)) = Imported.nat_S z with
      | Logic.eq_refl => Logic.eq_refl
      end
  end.

(* Prove addition commutativity for imported nat - needed because Coq and Lean multiply differently *)
Fixpoint imported_add_0_r (x : imported_nat) : Imported.Nat_add x Imported.nat_O = x :=
  match x with
  | Imported.nat_O => Logic.eq_refl
  | Imported.nat_S x' =>
      match imported_add_0_r x' in (_ = z) return Imported.nat_S (Imported.Nat_add x' Imported.nat_O) = Imported.nat_S z with
      | Logic.eq_refl => Logic.eq_refl
      end
  end.

Fixpoint imported_add_S_r (x y : imported_nat) : Imported.Nat_add x (Imported.nat_S y) = Imported.nat_S (Imported.Nat_add x y) :=
  match x with
  | Imported.nat_O => Logic.eq_refl
  | Imported.nat_S x' =>
      match imported_add_S_r x' y in (_ = z) return Imported.nat_S (Imported.Nat_add x' (Imported.nat_S y)) = Imported.nat_S z with
      | Logic.eq_refl => Logic.eq_refl
      end
  end.

Fixpoint imported_add_comm (x y : imported_nat) : Imported.Nat_add x y = Imported.Nat_add y x :=
  match x as x0 return Imported.Nat_add x0 y = Imported.Nat_add y x0 with
  | Imported.nat_O => 
      Logic.eq_sym (imported_add_0_r y)
  | Imported.nat_S x' =>
      (* Goal: S (Nat_add x' y) = Nat_add y (S x') *)
      (* Step 1: S (Nat_add x' y) = S (Nat_add y x') by IH *)
      (* Step 2: S (Nat_add y x') = Nat_add y (S x') by eq_sym (imported_add_S_r) *)
      Logic.eq_trans
        (match imported_add_comm x' y in (_ = z) 
           return Imported.nat_S (Imported.Nat_add x' y) = Imported.nat_S z
         with
         | Logic.eq_refl => Logic.eq_refl
         end)
        (Logic.eq_sym (imported_add_S_r y x'))
  end.

(* Then prove multiplication compatibility *)
(* Our Lean's Nat_mul (nat_S n) m = Nat_add m (Nat_mul n m), same as Coq's (S n) * m = m + n * m *)
Fixpoint nat_mul_compat (x y : Datatypes.nat) {struct x} :
  nat_to_imported (x * y) = Imported.Nat_mul (nat_to_imported x) (nat_to_imported y) :=
  match x as x0 return nat_to_imported (x0 * y) = Imported.Nat_mul (nat_to_imported x0) (nat_to_imported y) with
  | O => Logic.eq_refl
  | Datatypes.S x' =>
      (* Goal: nat_to_imported (y + x' * y) = Nat_add (nat_to_imported y) (Nat_mul x'_i y_i) *)
      Logic.eq_trans
        (nat_add_compat y (x' * y))
        (match nat_mul_compat x' y in (_ = z) 
           return Imported.Nat_add (nat_to_imported y) (nat_to_imported (x' * y)) = 
                  Imported.Nat_add (nat_to_imported y) z
         with
         | Logic.eq_refl => Logic.eq_refl
         end)
  end.

Definition Nat_mul_iso_aux (x1 x3 : Datatypes.nat) : 
  IsomorphismDefinitions.eq (nat_to_imported (x1 * x3)) (imported_Nat_mul (nat_to_imported x1) (nat_to_imported x3)).
Proof.
  pose proof (nat_mul_compat x1 x3) as H.
  rewrite H.
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance Nat_mul_iso : forall (x1 : Datatypes.nat) (x2 : imported_nat), rel_iso nat_iso x1 x2 -> forall (x3 : Datatypes.nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> rel_iso nat_iso (x1 * x3) (imported_Nat_mul x2 x4).
Proof.
  intros n1 n2 H12 n3 n4 H34.
  constructor. simpl.
  eapply eq_trans.
  { apply seq_of_eq. apply nat_mul_compat. }
  apply f_equal2.
  - exact (proj_rel_iso H12). 
  - exact (proj_rel_iso H34).
Defined.

Instance: KnownConstant Nat.mul := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Nat_mul := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Nat.mul Nat_mul_iso := {}.
Instance: IsoStatementProofBetween Nat.mul Imported.Nat_mul Nat_mul_iso := {}.