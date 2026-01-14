From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_corelib__U_init__U_logic__eq__iso Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.

Definition imported_Original_LF__DOT__Maps_LF_Maps_t__update__same : forall (x : Type) (x0 : imported_String_string -> x) (x1 : imported_String_string),
  imported_Corelib_Init_Logic_eq (fun x8 : imported_String_string => imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x2 : imported_String_string => x0 x2) x1 (x0 x1) x8)
    (fun x8 : imported_String_string => x0 x8) := Imported.Original_LF__DOT__Maps_LF_Maps_t__update__same.
Instance Original_LF__DOT__Maps_LF_Maps_t__update__same_iso : forall (x1 x2 : Type) (hx : Iso x1 x2) (x3 : Original.LF_DOT_Maps.LF.Maps.total_map x1) (x4 : imported_String_string -> x2)
    (hx0 : forall (x5 : String.string) (x6 : imported_String_string), @rel_iso String.string imported_String_string String_string_iso x5 x6 -> @rel_iso x1 x2 hx (x3 x5) (x4 x6)) 
    (x5 : String.string) (x6 : imported_String_string) (hx1 : @rel_iso String.string imported_String_string String_string_iso x5 x6),
  @rel_iso (@Original.LF_DOT_Maps.LF.Maps.t_update x1 x3 x5 (x3 x5) = x3)
    (@imported_Corelib_Init_Logic_eq (imported_String_string -> x2)
       (fun x8 : imported_String_string => @imported_Original_LF__DOT__Maps_LF_Maps_t__update x2 (fun x : imported_String_string => x4 x) x6 (x4 x6) x8) (fun x8 : imported_String_string => x4 x8))
    (@Corelib_Init_Logic_eq_iso (String.string -> x1) (imported_String_string -> x2) (@IsoArrow String.string imported_String_string String_string_iso x1 x2 hx)
       (@Original.LF_DOT_Maps.LF.Maps.t_update x1 x3 x5 (x3 x5))
       (fun x8 : imported_String_string => @imported_Original_LF__DOT__Maps_LF_Maps_t__update x2 (fun x : imported_String_string => x4 x) x6 (x4 x6) x8)
       (@IsoFunND String.string imported_String_string String_string_iso x1 x2 hx (@Original.LF_DOT_Maps.LF.Maps.t_update x1 x3 x5 (x3 x5))
          (fun x8 : imported_String_string => @imported_Original_LF__DOT__Maps_LF_Maps_t__update x2 (fun x : imported_String_string => x4 x) x6 (x4 x6) x8)
          (fun (x7 : String.string) (x8 : imported_String_string) (hx2 : @rel_iso String.string imported_String_string String_string_iso x7 x8) =>
           @unwrap_sprop
             (@rel_iso x1 x2 hx (@Original.LF_DOT_Maps.LF.Maps.t_update x1 x3 x5 (x3 x5) x7)
                (@imported_Original_LF__DOT__Maps_LF_Maps_t__update x2 (fun x : imported_String_string => x4 x) x6 (x4 x6) x8))
             (@Original_LF__DOT__Maps_LF_Maps_t__update_iso x1 x2 (@IsoIso true x1 x2 hx) x3 (fun x : imported_String_string => x4 x)
                (fun (x9 : String.string) (x10 : imported_String_string) (hx3 : @rel_iso String.string imported_String_string String_string_iso x9 x10) => {| unwrap_sprop := hx0 x9 x10 hx3 |}) x5 x6
                hx1 (x3 x5) (x4 x6) {| unwrap_sprop := hx0 x5 x6 hx1 |} x7 x8 hx2)))
       x3 (fun x8 : imported_String_string => x4 x8)
       (@IsoFunND String.string imported_String_string String_string_iso x1 x2 hx x3 (fun x8 : imported_String_string => x4 x8)
          (fun (x7 : String.string) (x8 : imported_String_string) (hx2 : @rel_iso String.string imported_String_string String_string_iso x7 x8) => hx0 x7 x8 hx2)))
    (Original.LF_DOT_Maps.LF.Maps.t_update_same x1 x3 x5) (@imported_Original_LF__DOT__Maps_LF_Maps_t__update__same x2 x4 x6).
Proof.
  intros.
  unfold rel_iso. simpl.
  (* Both sides are in SProp, so we can use SProp proof irrelevance *)
  apply IsomorphismDefinitions.eq_refl.
Qed.
Instance: KnownConstant Original.LF_DOT_Maps.LF.Maps.t_update_same := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Maps_LF_Maps_t__update__same := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Maps.LF.Maps.t_update_same Original_LF__DOT__Maps_LF_Maps_t__update__same_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Maps.LF.Maps.t_update_same Imported.Original_LF__DOT__Maps_LF_Maps_t__update__same Original_LF__DOT__Maps_LF_Maps_t__update__same_iso := {}.