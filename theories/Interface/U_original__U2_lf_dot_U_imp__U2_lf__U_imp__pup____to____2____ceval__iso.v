From Stdlib Require Import Derive.
From IsomorphismChecker Require Import IsomorphismStatementAutomationDefinitions EqualityLemmas IsomorphismDefinitions.
Import IsomorphismChecker.EqualityLemmas.IsoEq.
#[local] Unset Universe Polymorphism.
#[local] Set Implicit Arguments.
#[local] Hint Constants Opaque : typeclass_instances.
From IsomorphismChecker Require Original.

From IsomorphismChecker Require Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__pup____to____n__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_y__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__ceval__iso Interface.U_s__iso Interface.__0__iso Interface.true__iso.

Module Export CodeBlocks.

  Export (hints) Interface.U_ascii__ascii__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__pup____to____n__iso Interface.U_string__string__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_y__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso Interface.U_string__U_emptyU_string__iso Interface.U_string__U_string__iso Interface.bool__iso Interface.U_ascii__U_ascii__iso Interface.false__iso Interface.nat__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__ceval__iso Interface.U_s__iso Interface.__0__iso Interface.true__iso.

  Export Interface.U_ascii__ascii__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__pup____to____n__iso.CodeBlocks Interface.U_string__string__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_y__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.CodeBlocks Interface.U_string__U_emptyU_string__iso.CodeBlocks Interface.U_string__U_string__iso.CodeBlocks Interface.bool__iso.CodeBlocks Interface.U_ascii__U_ascii__iso.CodeBlocks Interface.false__iso.CodeBlocks Interface.nat__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.CodeBlocks Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__ceval__iso.CodeBlocks Interface.U_s__iso.CodeBlocks Interface.__0__iso.CodeBlocks Interface.true__iso.CodeBlocks.

End CodeBlocks.

Module Type Args := Interface.U_ascii__ascii__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__com__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__pup____to____n__iso.Interface <+ Interface.U_string__string__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_x__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__U_y__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__total____map__iso.Interface <+ Interface.U_original__U2_lf_dot_U_maps__U2_lf__U_maps__t____update__iso.Interface <+ Interface.U_string__U_emptyU_string__iso.Interface <+ Interface.U_string__U_string__iso.Interface <+ Interface.bool__iso.Interface <+ Interface.U_ascii__U_ascii__iso.Interface <+ Interface.false__iso.Interface <+ Interface.nat__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__empty____st__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__state__iso.Interface <+ Interface.U_original__U2_lf_dot_U_imp__U2_lf__U_imp__ceval__iso.Interface <+ Interface.U_s__iso.Interface <+ Interface.__0__iso.Interface <+ Interface.true__iso.Interface.

Module Type Interface (Import args : Args).

Parameter imported_Original_LF__DOT__Imp_LF_Imp_pup__to__2__ceval : imported_Original_LF__DOT__Imp_LF_Imp_ceval imported_Original_LF__DOT__Imp_LF_Imp_pup__to__n
    (fun x : imported_String_string =>
     imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x0 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x0) imported_Original_LF__DOT__Imp_LF_Imp_X
       (imported_S (imported_S imported_0)) x)
    (fun x : imported_String_string =>
     imported_Original_LF__DOT__Maps_LF_Maps_t__update
       (fun x0 : imported_String_string =>
        imported_Original_LF__DOT__Maps_LF_Maps_t__update
          (fun x1 : imported_String_string =>
           imported_Original_LF__DOT__Maps_LF_Maps_t__update
             (fun x2 : imported_String_string =>
              imported_Original_LF__DOT__Maps_LF_Maps_t__update
                (fun x3 : imported_String_string =>
                 imported_Original_LF__DOT__Maps_LF_Maps_t__update
                   (fun x4 : imported_String_string =>
                    imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x5 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x5) imported_Original_LF__DOT__Imp_LF_Imp_X
                      (imported_S (imported_S imported_0)) x4)
                   imported_Original_LF__DOT__Imp_LF_Imp_Y imported_0 x3)
                imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S (imported_S imported_0)) x2)
             imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S imported_0) x1)
          imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S (imported_S (imported_S imported_0))) x0)
       imported_Original_LF__DOT__Imp_LF_Imp_X imported_0 x).
Parameter Original_LF__DOT__Imp_LF_Imp_pup__to__2__ceval_iso : rel_iso
    (Original_LF__DOT__Imp_LF_Imp_ceval_iso Original_LF__DOT__Imp_LF_Imp_pup__to__n_iso (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2)
       (fun x : imported_String_string =>
        imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x0 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x0) imported_Original_LF__DOT__Imp_LF_Imp_X
          (imported_S (imported_S imported_0)) x)
       (fun (x1 : String.string) (x2 : imported_String_string) (hx : rel_iso String_string_iso x1 x2) =>
        unwrap_sprop
          (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso Original.LF_DOT_Imp.LF.Imp.empty_st (fun x : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x)
             (fun (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4) => {| unwrap_sprop := Original_LF__DOT__Imp_LF_Imp_empty__st_iso hx0 |})
             Original_LF__DOT__Imp_LF_Imp_X_iso 2 (imported_S (imported_S imported_0)) {| unwrap_sprop := S_iso (S_iso _0_iso) |} hx))
       (Original.LF_DOT_Maps.LF.Maps.t_update
          (Original.LF_DOT_Maps.LF.Maps.t_update
             (Original.LF_DOT_Maps.LF.Maps.t_update
                (Original.LF_DOT_Maps.LF.Maps.t_update
                   (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2) Original.LF_DOT_Imp.LF.Imp.Y 0)
                   Original.LF_DOT_Imp.LF.Imp.Y 2)
                Original.LF_DOT_Imp.LF.Imp.X 1)
             Original.LF_DOT_Imp.LF.Imp.Y 3)
          Original.LF_DOT_Imp.LF.Imp.X 0)
       (fun x : imported_String_string =>
        imported_Original_LF__DOT__Maps_LF_Maps_t__update
          (fun x0 : imported_String_string =>
           imported_Original_LF__DOT__Maps_LF_Maps_t__update
             (fun x1 : imported_String_string =>
              imported_Original_LF__DOT__Maps_LF_Maps_t__update
                (fun x2 : imported_String_string =>
                 imported_Original_LF__DOT__Maps_LF_Maps_t__update
                   (fun x3 : imported_String_string =>
                    imported_Original_LF__DOT__Maps_LF_Maps_t__update
                      (fun x4 : imported_String_string =>
                       imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x5 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x5)
                         imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) x4)
                      imported_Original_LF__DOT__Imp_LF_Imp_Y imported_0 x3)
                   imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S (imported_S imported_0)) x2)
                imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S imported_0) x1)
             imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S (imported_S (imported_S imported_0))) x0)
          imported_Original_LF__DOT__Imp_LF_Imp_X imported_0 x)
       (fun (x1 : String.string) (x2 : imported_String_string) (hx : rel_iso String_string_iso x1 x2) =>
        unwrap_sprop
          (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso
             (Original.LF_DOT_Maps.LF.Maps.t_update
                (Original.LF_DOT_Maps.LF.Maps.t_update
                   (Original.LF_DOT_Maps.LF.Maps.t_update
                      (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2) Original.LF_DOT_Imp.LF.Imp.Y 0)
                      Original.LF_DOT_Imp.LF.Imp.Y 2)
                   Original.LF_DOT_Imp.LF.Imp.X 1)
                Original.LF_DOT_Imp.LF.Imp.Y 3)
             (fun x : imported_String_string =>
              imported_Original_LF__DOT__Maps_LF_Maps_t__update
                (fun x0 : imported_String_string =>
                 imported_Original_LF__DOT__Maps_LF_Maps_t__update
                   (fun x3 : imported_String_string =>
                    imported_Original_LF__DOT__Maps_LF_Maps_t__update
                      (fun x4 : imported_String_string =>
                       imported_Original_LF__DOT__Maps_LF_Maps_t__update
                         (fun x5 : imported_String_string =>
                          imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x6 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x6)
                            imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) x5)
                         imported_Original_LF__DOT__Imp_LF_Imp_Y imported_0 x4)
                      imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S (imported_S imported_0)) x3)
                   imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S imported_0) x0)
                imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S (imported_S (imported_S imported_0))) x)
             (fun (x3 : String.string) (x4 : imported_String_string) (hx0 : rel_iso String_string_iso x3 x4) =>
              {|
                unwrap_sprop :=
                  unwrap_sprop
                    (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso
                       (Original.LF_DOT_Maps.LF.Maps.t_update
                          (Original.LF_DOT_Maps.LF.Maps.t_update
                             (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2)
                                Original.LF_DOT_Imp.LF.Imp.Y 0)
                             Original.LF_DOT_Imp.LF.Imp.Y 2)
                          Original.LF_DOT_Imp.LF.Imp.X 1)
                       (fun x : imported_String_string =>
                        imported_Original_LF__DOT__Maps_LF_Maps_t__update
                          (fun x0 : imported_String_string =>
                           imported_Original_LF__DOT__Maps_LF_Maps_t__update
                             (fun x5 : imported_String_string =>
                              imported_Original_LF__DOT__Maps_LF_Maps_t__update
                                (fun x6 : imported_String_string =>
                                 imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x7 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x7)
                                   imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) x6)
                                imported_Original_LF__DOT__Imp_LF_Imp_Y imported_0 x5)
                             imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S (imported_S imported_0)) x0)
                          imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S imported_0) x)
                       (fun (x5 : String.string) (x6 : imported_String_string) (hx1 : rel_iso String_string_iso x5 x6) =>
                        {|
                          unwrap_sprop :=
                            unwrap_sprop
                              (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso
                                 (Original.LF_DOT_Maps.LF.Maps.t_update
                                    (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2)
                                       Original.LF_DOT_Imp.LF.Imp.Y 0)
                                    Original.LF_DOT_Imp.LF.Imp.Y 2)
                                 (fun x : imported_String_string =>
                                  imported_Original_LF__DOT__Maps_LF_Maps_t__update
                                    (fun x0 : imported_String_string =>
                                     imported_Original_LF__DOT__Maps_LF_Maps_t__update
                                       (fun x7 : imported_String_string =>
                                        imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x8 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x8)
                                          imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) x7)
                                       imported_Original_LF__DOT__Imp_LF_Imp_Y imported_0 x0)
                                    imported_Original_LF__DOT__Imp_LF_Imp_Y (imported_S (imported_S imported_0)) x)
                                 (fun (x7 : String.string) (x8 : imported_String_string) (hx2 : rel_iso String_string_iso x7 x8) =>
                                  {|
                                    unwrap_sprop :=
                                      unwrap_sprop
                                        (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso
                                           (Original.LF_DOT_Maps.LF.Maps.t_update (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2)
                                              Original.LF_DOT_Imp.LF.Imp.Y 0)
                                           (fun x : imported_String_string =>
                                            imported_Original_LF__DOT__Maps_LF_Maps_t__update
                                              (fun x0 : imported_String_string =>
                                               imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x9 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x9)
                                                 imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) x0)
                                              imported_Original_LF__DOT__Imp_LF_Imp_Y imported_0 x)
                                           (fun (x9 : String.string) (x10 : imported_String_string) (hx3 : rel_iso String_string_iso x9 x10) =>
                                            {|
                                              unwrap_sprop :=
                                                unwrap_sprop
                                                  (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso
                                                     (Original.LF_DOT_Maps.LF.Maps.t_update Original.LF_DOT_Imp.LF.Imp.empty_st Original.LF_DOT_Imp.LF.Imp.X 2)
                                                     (fun x : imported_String_string =>
                                                      imported_Original_LF__DOT__Maps_LF_Maps_t__update (fun x0 : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x0)
                                                        imported_Original_LF__DOT__Imp_LF_Imp_X (imported_S (imported_S imported_0)) x)
                                                     (fun (x11 : String.string) (x12 : imported_String_string) (hx4 : rel_iso String_string_iso x11 x12) =>
                                                      {|
                                                        unwrap_sprop :=
                                                          unwrap_sprop
                                                            (Original_LF__DOT__Maps_LF_Maps_t__update_iso nat_iso Original.LF_DOT_Imp.LF.Imp.empty_st
                                                               (fun x : imported_String_string => imported_Original_LF__DOT__Imp_LF_Imp_empty__st x)
                                                               (fun (x13 : String.string) (x14 : imported_String_string) (hx5 : rel_iso String_string_iso x13 x14) =>
                                                                {| unwrap_sprop := Original_LF__DOT__Imp_LF_Imp_empty__st_iso hx5 |})
                                                               Original_LF__DOT__Imp_LF_Imp_X_iso 2 (imported_S (imported_S imported_0)) {| unwrap_sprop := S_iso (S_iso _0_iso) |} hx4)
                                                      |})
                                                     Original_LF__DOT__Imp_LF_Imp_Y_iso 0 imported_0 {| unwrap_sprop := _0_iso |} hx3)
                                            |})
                                           Original_LF__DOT__Imp_LF_Imp_Y_iso 2 (imported_S (imported_S imported_0)) {| unwrap_sprop := S_iso (S_iso _0_iso) |} hx2)
                                  |})
                                 Original_LF__DOT__Imp_LF_Imp_X_iso 1 (imported_S imported_0) {| unwrap_sprop := S_iso _0_iso |} hx1)
                        |})
                       Original_LF__DOT__Imp_LF_Imp_Y_iso 3 (imported_S (imported_S (imported_S imported_0))) {| unwrap_sprop := S_iso (S_iso (S_iso _0_iso)) |} hx0)
              |})
             Original_LF__DOT__Imp_LF_Imp_X_iso 0 imported_0 {| unwrap_sprop := _0_iso |} hx)))
    Original.LF_DOT_Imp.LF.Imp.pup_to_2_ceval imported_Original_LF__DOT__Imp_LF_Imp_pup__to__2__ceval.
Existing Instance Original_LF__DOT__Imp_LF_Imp_pup__to__2__ceval_iso.
#[export] Hint Extern 0 (IsoStatementProofFor Original.LF_DOT_Imp.LF.Imp.pup_to_2_ceval ?x) => unify x Original_LF__DOT__Imp_LF_Imp_pup__to__2__ceval_iso; constructor : typeclass_instances.
#[export] Hint Extern 0 (IsoStatementProofBetween Original.LF_DOT_Imp.LF.Imp.pup_to_2_ceval imported_Original_LF__DOT__Imp_LF_Imp_pup__to__2__ceval ?x) => unify x Original_LF__DOT__Imp_LF_Imp_pup__to__2__ceval_iso; constructor : typeclass_instances.


End Interface.