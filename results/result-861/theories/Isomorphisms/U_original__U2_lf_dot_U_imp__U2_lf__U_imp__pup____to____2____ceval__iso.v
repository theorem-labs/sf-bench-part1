From IsomorphismChecker Require Import AutomationDefinitions IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsoEq.
From LeanImport Require Import Lean.
#[local] Set Universe Polymorphism.
#[local] Set Implicit Arguments.
From IsomorphismChecker Require Original Imported.
(* Print Imported. *)
Typeclasses Opaque rel_iso. (* for speed *)


From IsomorphismChecker Require Export Isomorphisms.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso Isomorphisms.__0__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_y__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__ceval__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso Isomorphisms.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__pup____to____n__iso Isomorphisms.U_s__iso.

Definition imported_Original_LF__DOT__Imp_LF_Imp_pup__to__2__ceval : imported_Original_LF__DOT__Imp_LF_Imp_ceval imported_Original_LF__DOT__Imp_LF_Imp_pup__to__n
    (fun x : imported_String_string =>
     imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H) imported_Original_LF__DOT__Imp_LF_Imp_X
       (imported_S (imported_S imported_0)) x)
    (fun x : imported_String_string =>
     imported_Original_LF__DOT__Maps_LF_Maps_t__update
       (fun H : imported_String_string =>
        imported_Original_LF__DOT__Maps_LF_Maps_t__update
          (fun H0 : imported_String_string =>
           imported_Original_LF__DOT__Maps_LF_Maps_t__update
             (fun H1 : imported_String_string =>
              imported_Original_LF__DOT__Maps_LF_Maps_t__update
                (fun H2 : imported_String_string =>
                 imported_Original_LF__DOT__Maps_LF_Maps_t__update
                   (fun H3 : imported_String_string =>
                    imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H4 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H4) imported_Original_LF__DOT__Imp_LF_Imp_X
                      (imported_S (imported_S imported_0)) H3)
                   imported_Original_LF__DOT__Imp_LF_Imp_Y imported_0 H2)
                imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S (imported_S imported_0)) H1)
             imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S imported_0) H0)
          imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S (imported_S (imported_S imported_0))) H)
       imported_Original_LF__DOT__Imp_LF_Imp_X imported_0 x) := Imported.Original_LF__DOT__Imp_LF_Imp_pup__to__2__ceval.
Instance Original_LF__DOT__Imp_LF_Imp_pup__to__2__ceval_iso : rel_iso
    (Original_LF__DOT__Imp_LF_Imp_ceval_iso Original_LF__DOT__Imp_LF_Imp_pup__to__n_iso (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X (2%nat))
       (fun x : imported_String_string =>
        imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H) imported_Original_LF__DOT__Imp_LF_Imp_X
          (imported_S (imported_S imported_0)) x)
       (fun (x1 : String.string) (x2 : imported_String_string) (hx : rel_iso String_string_iso x1 x2) =>
        unwrap_sprop
          (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso Original.LF_DOT_Imp.LF.Imp.empty_st (fun H : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H)
             (fun (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4) => {| unwrap_sprop := Original_LF__DOT__Imp_LF_Imp_empty__st_iso hx0 |})
             Original_LF__DOT__Imp_LF_Imp_X_iso (2%nat) (imported_S (imported_S imported_0)) {| unwrap_sprop := S_iso (S_iso _0_iso) |} hx))
       (Original.LF_DOT_Maps.LF.Maps.t_update
          (Original.LF_DOT_Maps.LF.Maps.t_update
             (Original.LF_DOT_Maps.LF.Maps.t_update
                (Original.LF_DOT_Maps.LF.Maps.t_update
                   (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X (2%nat)) Original.LF_DOT_Imp.LF.Imp.Y (0%nat))
                   Original.LF_DOT_Imp.LF.Imp.Y (2%nat))
                Original.LF_DOT_Imp.LF.Imp.X (1%nat))
             Original.LF_DOT_Imp.LF.Imp.Y (3%nat))
          Original.LF_DOT_Imp.LF.Imp.X (0%nat))
       (fun x : imported_String_string =>
        imported_Original_LF__DOT__Maps_LF_Maps_t__update
          (fun H : imported_String_string =>
           imported_Original_LF__DOT__Maps_LF_Maps_t__update
             (fun H0 : imported_String_string =>
              imported_Original_LF__DOT__Maps_LF_Maps_t__update
                (fun H1 : imported_String_string =>
                 imported_Original_LF__DOT__Maps_LF_Maps_t__update
                   (fun H2 : imported_String_string =>
                    imported_Original_LF__DOT__Maps_LF_Maps_t__update
                      (fun H3 : imported_String_string =>
                       imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H4 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H4)
                         imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) H3)
                      imported_Original_LF__DOT__Imp_LF_Imp_Y imported_0 H2)
                   imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S (imported_S imported_0)) H1)
                imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S imported_0) H0)
             imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S (imported_S (imported_S imported_0))) H)
          imported_Original_LF__DOT__Imp_LF_Imp_X imported_0 x)
       (fun (x1 : String.string) (x2 : imported_String_string) (hx : rel_iso String_string_iso x1 x2) =>
        unwrap_sprop
          (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso
             (Original.LF_DOT_Maps.LF.Maps.t_update
                (Original.LF_DOT_Maps.LF.Maps.t_update
                   (Original.LF_DOT_Maps.LF.Maps.t_update
                      (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X (2%nat)) Original.LF_DOT_Imp.LF.Imp.Y (0%nat))
                      Original.LF_DOT_Imp.LF.Imp.Y (2%nat))
                   Original.LF_DOT_Imp.LF.Imp.X (1%nat))
                Original.LF_DOT_Imp.LF.Imp.Y (3%nat))
             (fun H : imported_String_string =>
              imported_Original_LF__DOT__Maps_LF_Maps_t__update
                (fun H0 : imported_String_string =>
                 imported_Original_LF__DOT__Maps_LF_Maps_t__update
                   (fun H1 : imported_String_string =>
                    imported_Original_LF__DOT__Maps_LF_Maps_t__update
                      (fun H2 : imported_String_string =>
                       imported_Original_LF__DOT__Maps_LF_Maps_t__update
                         (fun H3 : imported_String_string =>
                          imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H4 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H4)
                            imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) H3)
                         imported_Original_LF__DOT__Imp_LF_Imp_Y imported_0 H2)
                      imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S (imported_S imported_0)) H1)
                   imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S imported_0) H0)
                imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S (imported_S (imported_S imported_0))) H)
             (fun (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4) =>
              {|
                unwrap_sprop :=
                  unwrap_sprop
                    (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso
                       (Original.LF_DOT_Maps.LF.Maps.t_update
                          (Original.LF_DOT_Maps.LF.Maps.t_update
                             (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X (2%nat))
                                Original.LF_DOT_Imp.LF.Imp.Y (0%nat))
                             Original.LF_DOT_Imp.LF.Imp.Y (2%nat))
                          Original.LF_DOT_Imp.LF.Imp.X (1%nat))
                       (fun H : imported_String_string =>
                        imported_Original_LF__DOT__Maps_LF_Maps_t__update
                          (fun H0 : imported_String_string =>
                           imported_Original_LF__DOT__Maps_LF_Maps_t__update
                             (fun H1 : imported_String_string =>
                              imported_Original_LF__DOT__Maps_LF_Maps_t__update
                                (fun H2 : imported_String_string =>
                                 imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H3 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H3)
                                   imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) H2)
                                imported_Original_LF__DOT__Imp_LF_Imp_Y imported_0 H1)
                             imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S (imported_S imported_0)) H0)
                          imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S imported_0) H)
                       (fun (x5 : String.string) (x6 : imported_String_string) (hx1 : rel_iso String_string_iso x5 x6) =>
                        {|
                          unwrap_sprop :=
                            unwrap_sprop
                              (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso
                                 (Original.LF_DOT_Maps.LF.Maps.t_update
                                    (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X (2%nat))
                                       Original.LF_DOT_Imp.LF.Imp.Y (0%nat))
                                    Original.LF_DOT_Imp.LF.Imp.Y (2%nat))
                                 (fun H : imported_String_string =>
                                  imported_Original_LF__DOT__Maps_LF_Maps_t__update
                                    (fun H0 : imported_String_string =>
                                     imported_Original_LF__DOT__Maps_LF_Maps_t__update
                                       (fun H1 : imported_String_string =>
                                        imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H2 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H2)
                                          imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) H1)
                                       imported_Original_LF__DOT__Imp_LF_Imp_Y imported_0 H0)
                                    imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S (imported_S imported_0)) H)
                                 (fun (x7 : String.string) (x8 : imported_String_string) (hx2 : rel_iso String_string_iso x7 x8) =>
                                  {|
                                    unwrap_sprop :=
                                      unwrap_sprop
                                        (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso
                                           (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X (2%nat))
                                              Original.LF_DOT_Imp.LF.Imp.Y (0%nat))
                                           (fun H : imported_String_string =>
                                            imported_Original_LF__DOT__Maps_LF_Maps_t__update
                                              (fun H0 : imported_String_string =>
                                               imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H1 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H1)
                                                 imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) H0)
                                              imported_Original_LF__DOT__Imp_LF_Imp_Y imported_0 H)
                                           (fun (x9 : String.string) (x10 : imported_String_string) (hx3 : rel_iso String_string_iso x9 x10) =>
                                            {|
                                              unwrap_sprop :=
                                                unwrap_sprop
                                                  (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso
                                                     (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X (2%nat))
                                                     (fun H : imported_String_string =>
                                                      imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun H0 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H0)
                                                        imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) H)
                                                     (fun (x11 : String.string) (x12 : imported_String_string) (hx4 : rel_iso String_string_iso x11 x12) =>
                                                      {|
                                                        unwrap_sprop :=
                                                          unwrap_sprop
                                                            (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso Original.LF_DOT_Imp.LF.Imp.empty_st
                                                               (fun H : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st H)
                                                               (fun (x13 : String.string) (x14 : imported_String_string) (hx5 : rel_iso String_string_iso x13 x14) =>
                                                                {| unwrap_sprop := Original_LF__DOT__Imp_LF_Imp_empty__st_iso hx5 |})
                                                               Original_LF__DOT__Imp_LF_Imp_X_iso (2%nat) (imported_S (imported_S imported_0)) {| unwrap_sprop := S_iso (S_iso _0_iso) |} hx4)
                                                      |})
                                                     Original_LF__DOT__Imp_LF_Imp_Y_iso (0%nat) imported_0 {| unwrap_sprop := _0_iso |} hx3)
                                            |})
                                           Original_LF__DOT__Imp_LF_Imp_Y_iso (2%nat) (imported_S (imported_S imported_0)) {| unwrap_sprop := S_iso (S_iso _0_iso) |} hx2)
                                  |})
                                 Original_LF__DOT__Imp_LF_Imp_X_iso (1%nat) (imported_S imported_0) {| unwrap_sprop := S_iso _0_iso |} hx1)
                        |})
                       Original_LF__DOT__Imp_LF_Imp_Y_iso (3%nat) (imported_S (imported_S (imported_S imported_0))) {| unwrap_sprop := S_iso (S_iso (S_iso _0_iso)) |} hx0)
              |})
             Original_LF__DOT__Imp_LF_Imp_X_iso (0%nat) imported_0 {| unwrap_sprop := _0_iso |} hx)))
    Original.LF_DOT_Imp.LF.Imp.pup_to_2_ceval imported_Original_LF__DOT__Imp_LF_Imp_pup__to__2__ceval.
Admitted.
Instance: KnownConstant Original.LF_DOT_Imp.LF.Imp.pup_to_2_ceval := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: KnownConstant Imported.Original_LF__DOT__Imp_LF_Imp_pup__to__2__ceval := {}. (* only needed when rel_iso is typeclasses opaque *)
Instance: IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.pup_to_2_ceval Original_LF__DOT__Imp_LF_Imp_pup__to__2__ceval_iso := {}.
Instance: IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.pup_to_2_ceval Imported.Original_LF__DOT__Imp_LF_Imp_pup__to__2__ceval Original_LF__DOT__Imp_LF_Imp_pup__to__2__ceval_iso := {}.