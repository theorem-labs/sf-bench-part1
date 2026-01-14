From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original.
From IsomorphismChecker Require Imported.
Typeclasses Opaque rel_iso.

From IsomorphismChecker Require Export Isomorphisms.U_true__iso.

(* Imported.Corelib_Init_Logic_eq_Prop is now in SProp *)
Definition imported_Corelib_Init_Logic_eq_Prop : forall x : SProp, x -> x -> SProp := @Imported.Corelib_Init_Logic_eq_Prop.

(* Use match on the SProp eq to get that the two to i x and to i y are definitionally equal *)
Definition from_seq_Prop {A : Type} {B : SProp} (i : Iso A B) {x y : A}
  (H : Imported.Corelib_Init_Logic_eq_Prop B (to i x) (to i y)) : x = y :=
  match H in (Imported.Corelib_Init_Logic_eq_Prop _ _ z) return (from i (to i x) = from i z) -> x = y with
  | Imported.Corelib_Init_Logic_eq_Prop_refl _ _ => fun pf =>
      match from_to i x in IsomorphismDefinitions.eq _ w return w = y with
      | IsomorphismDefinitions.eq_refl =>
        match from_to i y in IsomorphismDefinitions.eq _ w return from i (to i x) = w with
        | IsomorphismDefinitions.eq_refl => pf
        end
      end
  end Logic.eq_refl.

(* Build Iso using proof irrelevance for the roundtrip conditions *)
Definition Corelib_Init_Logic_eq_iso_Prop_aux (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (H34 : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (H56 : @rel_iso x1 x2 hx x5 x6)
   : Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6).
Proof.
  unfold rel_iso in H34, H56.
  pose (fwd := fun (Heq : x3 = x5) =>
    match H34 in (IsomorphismDefinitions.eq _ y4) return imported_Corelib_Init_Logic_eq_Prop y4 x6 with
    | IsomorphismDefinitions.eq_refl =>
      match H56 in (IsomorphismDefinitions.eq _ y6) return imported_Corelib_Init_Logic_eq_Prop (to hx x3) y6 with
      | IsomorphismDefinitions.eq_refl =>
        match Heq in (_ = y5) return imported_Corelib_Init_Logic_eq_Prop (to hx x3) (to hx y5) with
        | Logic.eq_refl => Imported.Corelib_Init_Logic_eq_Prop_refl _ _
        end
      end
    end).
  pose (bwd := fun (Hseq : imported_Corelib_Init_Logic_eq_Prop x4 x6) =>
    match H34 in (IsomorphismDefinitions.eq _ y4) return (imported_Corelib_Init_Logic_eq_Prop y4 x6 -> x3 = x5) with
    | IsomorphismDefinitions.eq_refl => fun Hseq' =>
      match H56 in (IsomorphismDefinitions.eq _ y6) return (imported_Corelib_Init_Logic_eq_Prop (to hx x3) y6 -> x3 = x5) with
      | IsomorphismDefinitions.eq_refl => fun Hseq'' => from_seq_Prop hx Hseq''
      end Hseq'
    end Hseq).
  unshelve eapply Build_Iso.
  - exact fwd.
  - exact bwd.
  - intro Hseq. reflexivity.
  - intro Heq. 
    pose proof (Stdlib.Logic.ProofIrrelevance.proof_irrelevance _ (bwd (fwd Heq)) Heq) as PIR.
    destruct PIR.
    apply IsomorphismDefinitions.eq_refl.
Defined.

Instance Corelib_Init_Logic_eq_iso_Prop : (forall (x1 : Type) (x2 : SProp) (hx : Iso x1 x2) (x3 : x1) (x4 : x2) (_ : @rel_iso x1 x2 hx x3 x4) (x5 : x1) (x6 : x2) (_ : @rel_iso x1 x2 hx x5 x6),
   Iso (@Corelib.Init.Logic.eq x1 x3 x5) (@imported_Corelib_Init_Logic_eq_Prop x2 x4 x6)) :=
  Corelib_Init_Logic_eq_iso_Prop_aux.

Instance: KnownConstant (@Imported.Corelib_Init_Logic_eq_Prop) := {}.
Instance: IsoStatementProofForWithSorts (HList.const Prop HList.nil) (@Corelib.Init.Logic.eq) Corelib_Init_Logic_eq_iso_Prop := {}.
Instance: IsoStatementProofBetween (@Corelib.Init.Logic.eq) (@Imported.Corelib_Init_Logic_eq_Prop) Corelib_Init_Logic_eq_iso_Prop := {}.
