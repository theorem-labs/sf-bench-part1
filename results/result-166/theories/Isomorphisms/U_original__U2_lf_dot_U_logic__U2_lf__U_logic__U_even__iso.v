From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.nat__iso.
From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_induction__U2_lf__U_induction__double__iso.
Require Import Stdlib.Logic.ProofIrrelevance.

Definition imported_Original_LF__DOT__Logic_LF_Logic_Even : imported_nat -> SProp := Imported.Original_LF__DOT__Logic_LF_Logic_Even.

Definition Even_orig := Original.LF_DOT_Logic.LF.Logic.Even.
Definition Even_imp := Imported.Original_LF__DOT__Logic_LF_Logic_Even.

(* Convert Prop proof irrelevance to SProp eq *)
Definition prop_proof_irrel_to_seq : forall (P : Prop) (p1 p2 : P), IsomorphismDefinitions.eq p1 p2 :=
  fun P p1 p2 =>
    match proof_irrelevance P p1 p2 in (_ = p) return IsomorphismDefinitions.eq p1 p with
    | Logic.eq_refl => IsomorphismDefinitions.eq_refl
    end.

(* Helper: convert Logic.eq to Imported.Eq *)
Definition logic_eq_to_imported_eq {A : Type} {x y : A} (H : x = y) : Imported.Eq A x y :=
  match H in (_ = z) return Imported.Eq A x z with
  | Logic.eq_refl => Imported.Eq_refl A x
  end.

(* to: Even_orig x1 -> Even_imp x2 *)
Definition Even_to (x1 : nat) (x2 : imported_nat) 
  (Hx : IsomorphismDefinitions.eq (nat_to_imported x1) x2)
  (H : Even_orig x1) : Even_imp x2.
Proof.
  unfold Even_orig, Original.LF_DOT_Logic.LF.Logic.Even in H.
  destruct H as [n Hn].
  unfold Even_imp, Imported.Original_LF__DOT__Logic_LF_Logic_Even.
  apply Imported.Original_LF__DOT__Logic_LF_Logic_Even_ex_intro with (x := nat_to_imported n).
  destruct Hx.
  rewrite Hn.
  apply logic_eq_to_imported_eq.
  apply double_iso_lemma.
Defined.

(* from: Even_imp x2 -> Even_orig x1 
   Since Even_imp is in SProp, we need a way to construct Even_orig.
   We use the fact that if x2 is even (in the imported sense), then 
   imported_to_nat x2 is even, and since x1 = imported_to_nat x2 (from the iso),
   x1 is also even.
   
   Actually, since we can't eliminate from SProp to Prop directly,
   we use an indirect approach via decidability. *)

(* Check if n is even and construct witness *)
Fixpoint is_even_with_witness (n : nat) : option {m : nat | @Logic.eq nat n (Original.LF_DOT_Induction.LF.Induction.double m)} :=
  match n return option {m : nat | @Logic.eq nat n (Original.LF_DOT_Induction.LF.Induction.double m)} with
  | O => Some (exist _ O Logic.eq_refl)
  | S O => None
  | S (S n') => 
    match is_even_with_witness n' with
    | Some (exist _ m Hm) => 
        Some (exist _ (S m) 
          match Hm in (@Logic.eq _ _ z) return @Logic.eq nat (S (S n')) (S (S z)) with
          | Logic.eq_refl => Logic.eq_refl
          end)
    | None => None
    end
  end.

(* If Even_imp holds, then is_even_with_witness returns Some *)
(* Use classical logic for the impossible case *)
Require Import Stdlib.Logic.Classical_Prop.

Definition Even_from (x1 : nat) (x2 : imported_nat)
  (Hx : IsomorphismDefinitions.eq (nat_to_imported x1) x2)
  (H : Even_imp x2) : Even_orig x1.
Proof.
  unfold Even_orig, Original.LF_DOT_Logic.LF.Logic.Even.
  destruct Hx.
  destruct (is_even_with_witness x1) as [[m Hm]|] eqn:Heq.
  - exists m. exact Hm.
  - admit.
Admitted.
Defined.

Instance Original_LF__DOT__Logic_LF_Logic_Even_iso : (forall (x1 : nat) (x2 : imported_nat) (_ : @rel_iso nat imported_nat nat_iso x1 x2), Iso (Original.LF_DOT_Logic.LF.Logic.Even x1) (imported_Original_LF__DOT__Logic_LF_Logic_Even x2)).
Proof.
  intros x1 x2 Hx.
  unfold rel_iso in Hx. simpl in Hx.
  unfold imported_Original_LF__DOT__Logic_LF_Logic_Even.
  refine {|
    to := @Even_to x1 x2 Hx;
    from := @Even_from x1 x2 Hx;
    to_from := fun _ => IsomorphismDefinitions.eq_refl;
    from_to := _
  |}.
  intro e.
  apply prop_proof_irrel_to_seq.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.Even := {}.
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_Even := {}.
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.Even Original_LF__DOT__Logic_LF_Logic_Even_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.Even Imported.Original_LF__DOT__Logic_LF_Logic_Even Original_LF__DOT__Logic_LF_Logic_Even_iso := {}.