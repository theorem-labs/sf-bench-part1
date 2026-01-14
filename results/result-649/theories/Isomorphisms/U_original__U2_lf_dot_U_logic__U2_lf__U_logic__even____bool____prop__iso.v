From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__even__iso Isomorphisms.U_original__U2_lf_dot_U_basics__U2_lf__U_basics__true__iso Isomorphisms.U_original__U2_lf_dot_U_logic__U2_lf__U_logic__U_even__iso Isomorphisms.iff__iso.

From Stdlib Require Import ProofIrrelevance.

Definition imported_Original_LF__DOT__Logic_LF_Logic_even__bool__prop : forall x : imported_nat,
  imported_iff (imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_even x) imported_Original_LF__DOT__Basics_LF_Basics_true)
    (imported_Original_LF__DOT__Logic_LF_Logic_Even x) := Imported.Original_LF__DOT__Logic_LF_Logic_even__bool__prop.

(* Helper to convert Prop proof irrelevance to SProp eq *)
Definition prop_irrel_to_seq {P : Prop} (p1 p2 : P) : IsomorphismDefinitions.eq p1 p2 :=
  match proof_irrelevance P p1 p2 in (_ = p) return IsomorphismDefinitions.eq p1 p with
  | Logic.eq_refl => IsomorphismDefinitions.eq_refl
  end.

Instance Original_LF__DOT__Logic_LF_Logic_even__bool__prop_iso : forall (x1 : nat) (x2 : imported_nat) (hx : rel_iso nat_iso x1 x2),
  rel_iso
    {|
      to := iff_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_even_iso hx) Original_LF__DOT__Basics_LF_Basics_true_iso) (Original_LF__DOT__Logic_LF_Logic_Even_iso hx);
      from := from (iff_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_even_iso hx) Original_LF__DOT__Basics_LF_Basics_true_iso) (Original_LF__DOT__Logic_LF_Logic_Even_iso hx));
      to_from :=
        fun
          x : imported_iff (imported_Corelib_Init_Logic_eq (imported_Original_LF__DOT__Basics_LF_Basics_even x2) imported_Original_LF__DOT__Basics_LF_Basics_true)
                (imported_Original_LF__DOT__Logic_LF_Logic_Even x2) =>
        to_from (iff_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_even_iso hx) Original_LF__DOT__Basics_LF_Basics_true_iso) (Original_LF__DOT__Logic_LF_Logic_Even_iso hx)) x;
      from_to :=
        fun x : Original.LF_DOT_Basics.LF.Basics.even x1 = Original.LF_DOT_Basics.LF.Basics.true <-> Original.LF_DOT_Logic.LF.Logic.Even x1 =>
        seq_p_of_t
          (from_to (iff_iso (Corelib_Init_Logic_eq_iso (Original_LF__DOT__Basics_LF_Basics_even_iso hx) Original_LF__DOT__Basics_LF_Basics_true_iso) (Original_LF__DOT__Logic_LF_Logic_Even_iso hx)) x)
    |} (Original.LF_DOT_Logic.LF.Logic.even_bool_prop x1) (imported_Original_LF__DOT__Logic_LF_Logic_even__bool__prop x2).
Proof.
  intros x1 x2 hx.
  (* Both Original.LF_DOT_Logic.LF.Logic.even_bool_prop and imported_Original_LF__DOT__Logic_LF_Logic_even__bool__prop 
     are in Prop/SProp respectively. Since they are proofs, we can use proof irrelevance. *)
  unfold rel_iso. simpl.
  (* The goal is to show that to applied to the original gives the imported version *)
  (* Since the result is in SProp, this is trivially true by SProp proof irrelevance *)
  apply IsomorphismDefinitions.eq_refl.
Defined.

Instance: KnownConstant Original.LF_DOT_Logic.LF.Logic.even_bool_prop := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Logic_LF_Logic_even__bool__prop := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Logic.LF.Logic.even_bool_prop Original_LF__DOT__Logic_LF_Logic_even__bool__prop_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Logic.LF.Logic.even_bool_prop Imported.Original_LF__DOT__Logic_LF_Logic_even__bool__prop Original_LF__DOT__Logic_LF_Logic_even__bool__prop_iso := {}.