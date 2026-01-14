From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.nat__iso.

Definition imported_Original_LF__DOT__Basics_LF_Basics_plus' : imported_nat -> imported_nat -> imported_nat := Imported.Original_LF__DOT__Basics_LF_Basics_plus'.

(* First prove that the two functions behave the same way *)
Fixpoint plus'_equiv (n m : nat) :
  nat_to_imported (Original.LF_DOT_Basics.LF.Basics.plus' n m) = 
  Imported.Original_LF__DOT__Basics_LF_Basics_plus' (nat_to_imported n) (nat_to_imported m) :=
  match n with
  | O => Coq.Init.Logic.eq_refl
  | S n' => match plus'_equiv n' m in (_ = r) 
            return (Imported.nat_S (nat_to_imported (Original.LF_DOT_Basics.LF.Basics.plus' n' m)) = 
                    Imported.nat_S r)
            with
            | Coq.Init.Logic.eq_refl => Coq.Init.Logic.eq_refl
            end
  end.

Instance Original_LF__DOT__Basics_LF_Basics_plus'_iso : forall (x1 : nat) (x2 : imported_nat),
  rel_iso nat_iso x1 x2 ->
  forall (x3 : nat) (x4 : imported_nat), rel_iso nat_iso x3 x4 -> rel_iso nat_iso (Original.LF_DOT_Basics.LF.Basics.plus' x1 x3) (imported_Original_LF__DOT__Basics_LF_Basics_plus' x2 x4).
Proof.
  intros x1 x2 H12 x3 x4 H34.
  unfold rel_iso in *.
  simpl in *.
  unfold imported_Original_LF__DOT__Basics_LF_Basics_plus'.
  (* We need to show: eq (nat_to_imported (plus' x1 x3)) (Imported.plus' x2 x4) *)
  (* We know: eq (nat_to_imported x1) x2 and eq (nat_to_imported x3) x4 *)
  (* plus'_equiv shows: nat_to_imported (plus' x1 x3) = Imported.plus' (nat_to_imported x1) (nat_to_imported x3) *)
  apply (eq_trans (seq_of_eq (plus'_equiv x1 x3))).
  apply (f_equal2 (fun a b => Imported.Original_LF__DOT__Basics_LF_Basics_plus' a b) H12 H34).
Qed.

Instance: KnownConstant Original.LF_DOT_Basics.LF.Basics.plus' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Basics_LF_Basics_plus' := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Basics.LF.Basics.plus' Original_LF__DOT__Basics_LF_Basics_plus'_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Basics.LF.Basics.plus' Imported.Original_LF__DOT__Basics_LF_Basics_plus' Original_LF__DOT__Basics_LF_Basics_plus'_iso := {}.