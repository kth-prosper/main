;
val _ = overload_on("priv_mode_constraints", ``priv_mode_constraints_v1``);
val priv_mode_constraints_def = priv_mode_constraints_v1_def;



val untouched_refl = store_thm(
    "untouched_refl",
    ``!gst s. untouched gst s s``,
    RW_TAC (srw_ss()) [untouched_def] THEN RW_TAC (srw_ss()) []);



val similarity_implies_equal_mode_thm = store_thm(
    "similarity_implies_equal_mode_thm", 
    ``! g s1 s2. (similar g s1 s2) ==> (ARM_MODE s1 = ARM_MODE s2)``,
    EVAL_TAC
      THEN RW_TAC (srw_ss()) []
      THEN SPEC_ASSUM_TAC (``!(ii:iiid). X``, [``<|proc:=0|>``])
      THEN FULL_SIMP_TAC (srw_ss()) []);


val similarity_implies_equal_av_thm = store_thm(
    "similarity_implies_equal_av_thm", 
    ``! g s1 s2. (similar g s1 s2) ==> (access_violation s1 = access_violation s2)``,
    EVAL_TAC
      THEN RW_TAC (srw_ss()) []);



(*  3-parts-lem *)

val keep_mode_relation_def = Define `keep_mode_relation comp i1 i2 = 
  (!g s s' x. (mmu_requirements s g) ==> (i1 s) ==> (comp s = ValueState x s') ==> (i2 s'))`;

val keep_similar_relation_def = Define `keep_similar_relation comp invr1 y = 
    !g s1 s2.
    mmu_requirements s1 g    ==>
    mmu_requirements s2 g    ==>
    similar g s1 s2          ==>
    (y  g s1 s2)            ==>
    invr1 s1                 ==>
    invr1 s2                 ==>
    ((?a s1' s2'.((comp s1 = ValueState a s1') /\  (comp s2 = ValueState a s2') /\
           (y  g s1' s2') /\        (similar g s1' s2')))
\/   (? e. (comp s1 = Error e) /\ (comp s2 = Error e)))`;

val keep_untouched_relation_def = Define `keep_untouched_relation comp invr1 f =
    !g s s' a. (mmu_requirements s g) ==> (invr1 s) ==> (comp s = ValueState a s') ==> ((untouched g s s') /\  (f g s s'))`;

val three_parts_thm = store_thm(
    "three_parts_thm",
    ``!comp i1 i2 f y. (keep_mode_relation comp i1 i2) ==> (keep_similar_relation comp i1 y) ==> (keep_untouched_relation comp i1 f) ==> (preserve_relation_mmu comp i1 i2 f y)``,
    RW_TAC (srw_ss()) [preserve_relation_mmu_def, keep_mode_relation_def, keep_similar_relation_def, keep_untouched_relation_def] THEN METIS_TAC []);

val refl_rel_def = Define `refl_rel y = (!gg ss. y gg ss ss)`;

val downgrade_thm = store_thm (
    "downgrade_thm",
    ``!comp i1 i2 f y. (preserve_relation_mmu comp i1 i2 f y) ==> (refl_rel y)
       ==> (keep_mode_relation comp i1 i2 /\ keep_similar_relation comp i1 y /\ keep_untouched_relation comp i1 f)``,
    RW_TAC (srw_ss()) [refl_rel_def, preserve_relation_mmu_def, keep_mode_relation_def, keep_similar_relation_def, keep_untouched_relation_def]
       THEN RES_TAC
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN (TRY (METIS_TAC []))
       THEN ASSUME_TAC (SPECL [``g:word32``, ``s:arm_state``] similar_refl)
       THEN SPEC_ASSUM_TAC (``!gg ss. y gg ss``, [``g:word32``, ``s:arm_state``])
       THEN RES_TAC
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN METIS_TAC []);


val comb_gen_lem = store_thm(
    "comb_gen_lem",
    ``!comp i1 i2 i3 i23 f y. (comb i2 i3 i23 \/ comb i3 i2 i23) ==> (preserve_relation_mmu comp i1 i2 f y) ==> (preserve_relation_mmu comp i1 i23 f y)``,
    RW_TAC (srw_ss()) [preserve_relation_mmu_def, comb_def]
        THEN METIS_TAC[]);


(* 
val seqT_preserve_relation_noabs_thm =
    store_thm ("seqT_preserve_relation_noabs_thm",
    ``! f1 f2 invr1 invr2 invr3 invr23 .
          (comb invr2 invr3 invr23)                        ==>
          (preserve_relation_mmu f1 (invr1) (invr2))       ==>
          (preserve_relation_mmu f2 (invr2) (invr3))
            ==>
          (preserve_relation_mmu (f1 >>= (\x. f2)) invr1 invr23)``,
    (RW_TAC (srw_ss()) [seqT_def,constT_def,preserve_relation_mmu_def,preserve_relation_mmu_abs_def]) 
    THEN (UNDISCH_ALL_TAC
       THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) []))
    THENL [UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
THEN RES_TAC
THEN IMP_RES_TAC untouched_trans
       THEN FULL_SIMP_TAC (srw_ss()) []
THEN METIS_TAC [untouched_trans, comb_rel_lem],
RW_TAC (srw_ss()) []
THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
       THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN Cases_on `invr1 s2`
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
       THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (srw_ss()) []
THEN Cases_on `f2 b`
THEN Cases_on `f2 b'`
THEN (NTAC 2 (RES_TAC
THEN IMP_RES_TAC untouched_trans
       THEN FULL_SIMP_TAC (srw_ss()) []
THEN IMP_RES_TAC untouched_mmu_setup_lem
THEN
TRY (PAT_ASSUM ``!g' s1'' s2''. X`` (fn th => ASSUME_TAC (SPECL [``g:bool[32]``, ``b:arm_state``, ``b':arm_state``] th)))
 THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []))
THEN METIS_TAC [comb_rel_lem],
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN Cases_on `invr1 s2`
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []]);
*)
;


val constT_unit_preserving_lem = store_thm(
    "constT_unit_preserving_lem",
    ``!invr:(arm_state->bool) uf uy.  (reflexive_comp  uf invr) ==> 
			      preserve_relation_mmu  (constT ()) invr invr uf uy``,
    RW_TAC (srw_ss()) [constT_def, preserve_relation_mmu_def, untouched_def, similar_def,reflexive_comp_def] THEN 
(RW_TAC (srw_ss()) [] ));




(*DIFF_OLI: the whole next part on forT (non-abs) *)

val SEQT_UNTOUCHED_TAC =
    UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) [seqT_def, keep_untouched_relation_def, trans_fun_def]
       THEN UNDISCH_ALL_TAC 
       THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) [])
       THEN UNDISCH_ALL_TAC 
       THEN RW_TAC (srw_ss()) [] 
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN IMP_RES_TAC untouched_mmu_setup_lem
       THEN RES_TAC
       THEN IMP_RES_TAC untouched_trans
       THEN FULL_SIMP_TAC (srw_ss()) [];


val forT_untouching_thm = store_thm(
    "forT_untouching_thm",
    ``!f k uf uy. 
            (trans_fun uf)
        ==> (reflexive_comp uf (assert_mode k))
        ==> (!a. keep_untouched_relation (f a) (assert_mode k) uf)
        ==> (!a. keep_mode_relation (f a) (assert_mode k) (assert_mode k))
        ==> (!l h. keep_untouched_relation (forT l h f) (assert_mode k) uf)``,
    REPEAT STRIP_TAC
      THEN Induct_on `h - l` 
      THENL [FULL_SIMP_TAC (srw_ss()) []
                THEN REPEAT STRIP_TAC
                THEN NTAC 2 (PURE_ONCE_REWRITE_TAC [forT_def, LET_DEF])
                THEN RW_TAC arith_ss [keep_untouched_relation_def, constT_def, seqT_def]
                THEN (REPEAT (PAT_ASSUM (``!(l:num). X``) (fn th => (ASSUME_TAC (SPEC ``l:num`` th)))))
                THEN REPEAT STRIP_TAC
                THEN SEQT_UNTOUCHED_TAC
                THEN FULL_SIMP_TAC (srw_ss()) [untouched_def, reflexive_comp_def]
                THEN RW_TAC (srw_ss()) [LET_DEF],
             FULL_SIMP_TAC (srw_ss()) []
                THEN REPEAT STRIP_TAC
                THEN PURE_ONCE_REWRITE_TAC [forT_def, LET_DEF]
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC arith_ss [constT_def]
                THEN `v = h - (l+1)` by FULL_SIMP_TAC arith_ss []
                THEN PAT_ASSUM ``!h l. X => Y`` (fn th => IMP_RES_TAC (SPECL [``h:num``, ``(l+1):num``] th))
                THEN REPEAT (PAT_ASSUM (``!(l:num). X``) (fn th => (ASSUME_TAC (SPEC ``l:num`` th))))
                THEN FULL_SIMP_TAC (srw_ss()) [keep_mode_relation_def]
                THEN REPEAT STRIP_TAC
                THEN SEQT_UNTOUCHED_TAC
                THEN METIS_TAC [assert_mode_def]]);


val SEQT_PRESERVE_TAC = fn F1 =>
    (RW_TAC (srw_ss()) [seqT_def,constT_def,keep_similar_relation_def,keep_untouched_relation_def, keep_mode_relation_def]
       THEN Cases_on [QUOTE (F1^" s1")]
       THEN Cases_on [QUOTE (F1^" s2")]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) [] 
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def]) 
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN RW_TAC (srw_ss()) []
       THEN `mmu_requirements b g` by METIS_TAC [untouched_mmu_setup_lem]
       THEN `mmu_requirements b' g` by METIS_TAC [untouched_mmu_setup_lem]
       THEN METIS_TAC []);


val SEQT_PRESERVE_BEGIN_TAC = fn F1 =>
    (RW_TAC (srw_ss()) [seqT_def,constT_def,keep_similar_relation_def,keep_untouched_relation_def, keep_mode_relation_def]
       THEN Cases_on [QUOTE (F1^" s1")]
       THEN Cases_on [QUOTE (F1^" s2")]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) [] 
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def]) 
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN RW_TAC (srw_ss()) []
       THEN `mmu_requirements b g` by METIS_TAC [untouched_mmu_setup_lem]
       THEN `mmu_requirements b' g` by METIS_TAC [untouched_mmu_setup_lem]);

val forT_similar_thm = store_thm(
    "forT_similar_thm",
    ``!f k uf uy. 
            (!a. keep_untouched_relation (f a) (assert_mode k) uf)
        ==> (!a. keep_mode_relation (f a) (assert_mode k) (assert_mode k))
        ==> (!a. keep_similar_relation (f a) (assert_mode k) uy)
        ==> (!l h. keep_similar_relation (forT l h f) (assert_mode k) uy)``,
    REPEAT STRIP_TAC
      THEN IMP_RES_TAC forT_untouching_thm
      THEN Induct_on `h - l` 
      THENL [FULL_SIMP_TAC (srw_ss()) []
                THEN (REPEAT STRIP_TAC)
                THEN (NTAC 2 (PURE_ONCE_REWRITE_TAC [forT_def, LET_DEF]))
                THEN RW_TAC arith_ss [keep_similar_relation_def, constT_def, seqT_def]
                THEN (REPEAT (PAT_ASSUM (``!(l:num). X``) (fn th => (ASSUME_TAC (SPEC ``l:num`` th)))))
                THEN (REPEAT STRIP_TAC)
                THEN UNDISCH_ALL_TAC
                THEN SEQT_PRESERVE_TAC "f l",


             FULL_SIMP_TAC (srw_ss()) []
                THEN REPEAT STRIP_TAC
                THEN PURE_ONCE_REWRITE_TAC [forT_def, LET_DEF]
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC arith_ss []
                THEN `v = h - (l+1)` by FULL_SIMP_TAC arith_ss []
                THEN PAT_ASSUM ``!h l. X => Y`` (fn th => IMP_RES_TAC (SPECL [``h:num``, ``(l+1):num``] th))
            (*    THEN PAT_ASSUM ``!l h. Z (x)`` (fn th => ASSUME_TAC (SPECL [``(l+1):num``, ``h:num``] th)) *)
                THEN REPEAT (PAT_ASSUM ``!(a:num). Z (x)`` (fn th => ASSUME_TAC (SPEC ``l:num`` th)))
                THEN REPEAT STRIP_TAC
                THEN UNDISCH_ALL_TAC
                THEN SEQT_PRESERVE_BEGIN_TAC "f l"
                THEN Cases_on `forT (l + 1) h f b`
                THEN Cases_on `forT (l + 1) h f b'`
                THEN FULL_SIMP_TAC (srw_ss()) [] 
                THEN PAT_ASSUM ``∀g s1 s2. mmu_requirements s1 g ⇒
                                           mmu_requirements s2 g ⇒
                                           similar g s1 s2 ⇒
                                           uy g s1 s2 ==>
                                           (invr s1) ==>
                                           (invr s2) ==>
                                   (∃a s1' s2'.
                                       (forT (l + 1) h f s1 = ValueState a s1') ∧
                                       (forT (l + 1) h f s2 = ValueState a s2') ∧ (uy g s1' s2') /\ similar g s1' s2') ∨
                                    ∃e.
                                       (forT (l + 1) h f s1 = Error e) ∧
                                       (forT (l + 1) h f s2 = Error e)``
                     (fn th => ASSUME_TAC (SPECL [``g:word32``, ``b:arm_state``, ``b':arm_state``] th))
                THEN RES_TAC
                THEN FULL_SIMP_TAC (srw_ss()) []
                THEN REPEAT IF_CASES_TAC THEN RW_TAC (srw_ss()) []
                THEN (`access_violation b'' = access_violation b'''` by METIS_TAC [similar_def])
                THEN FULL_SIMP_TAC (srw_ss()) []]);


val forT_mode_thm = store_thm(
    "forT_mode_thm",
    ``!f k uf. 
            (!a. keep_untouched_relation (f a) (assert_mode k) uf)
        ==> (!a. keep_mode_relation (f a) (assert_mode k) (assert_mode k))
        ==> (!l h. keep_mode_relation (forT l h f)  (assert_mode k) (assert_mode k))``,
    REPEAT STRIP_TAC
      THEN Induct_on `h - l` 
      THENL [FULL_SIMP_TAC (srw_ss()) []
                THEN REPEAT STRIP_TAC
                THEN NTAC 2 (PURE_ONCE_REWRITE_TAC [forT_def, LET_DEF])
                THEN RW_TAC arith_ss [keep_untouched_relation_def, constT_def, seqT_def]
                THEN (REPEAT (PAT_ASSUM (``!(l:num). X``) (fn th => (ASSUME_TAC (SPEC ``l:num`` th)))))
                THEN REPEAT STRIP_TAC
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC (srw_ss()) [seqT_def, keep_mode_relation_def]
                THEN UNDISCH_ALL_TAC 
                THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) [])
                THEN UNDISCH_ALL_TAC 
                THEN RW_TAC (srw_ss()) [] 
                THEN FULL_SIMP_TAC (srw_ss()) []
                THEN RES_TAC
                THEN FULL_SIMP_TAC (srw_ss()) [],
             FULL_SIMP_TAC (srw_ss()) []
                THEN REPEAT STRIP_TAC
                THEN PURE_ONCE_REWRITE_TAC [forT_def, LET_DEF]
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC arith_ss [constT_def]
                THEN `v = h - (l+1)` by FULL_SIMP_TAC arith_ss []
                THEN PAT_ASSUM ``!h l. X => Y`` (fn th => IMP_RES_TAC (SPECL [``h:num``, ``(l+1):num``] th))
                THEN REPEAT (PAT_ASSUM (``!(l:num). X``) (fn th => (ASSUME_TAC (SPEC ``l:num`` th))))
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC (srw_ss()) [seqT_def, keep_mode_relation_def]
                THEN UNDISCH_ALL_TAC 
                THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) [])
                THEN UNDISCH_ALL_TAC 
                THEN RW_TAC (srw_ss()) [] 
                THEN RES_TAC
                THEN FULL_SIMP_TAC (srw_ss()) [keep_untouched_relation_def]
                THEN RES_TAC
                THEN IMP_RES_TAC untouched_mmu_setup_lem
                THEN RES_TAC]);



val forT_preserves_user_relation_thm = store_thm(
    "forT_preserves_user_relation_thm",
    ``!f k uf uy. 
            (trans_fun uf)
        ==> (refl_rel uy)
        ==> (reflexive_comp uf (assert_mode k))
        ==> (!a. preserve_relation_mmu (f a) (assert_mode k) (assert_mode k) uf uy)
        ==> (!l h. preserve_relation_mmu (forT l h f) (assert_mode k) (assert_mode k) uf uy)``,
        METIS_TAC [forT_similar_thm, forT_mode_thm, forT_untouching_thm, three_parts_thm, downgrade_thm]);


val forT_preserving_thm = store_thm(
    "forT_preserving_thm",
    ``!f k uf uy. 
            (trans_fun uf)
        ==> (refl_rel uy)
        ==> (reflexive_comp uf (assert_mode k))
        ==> (preserve_relation_mmu_abs f (assert_mode k) (assert_mode k) uf uy)
        ==> (!l h. preserve_relation_mmu (forT l h f) (assert_mode k) (assert_mode k) uf uy)``,
   RW_TAC (srw_ss()) [] THEN METIS_TAC [forT_preserves_user_relation_thm, second_abs_lemma]);


(*************************************************)



val errorT_thm = store_thm("errorT_thm",
  ``! invr s f y. preserve_relation_mmu (errorT s) invr invr f y``,
 (RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def, assert_mode_def,errorT_def,untouched_def]));


val errorT_comb_thm = store_thm("errorT_comb_thm",
  ``! invr invr2 s f y. preserve_relation_mmu (errorT s) invr invr2 f y``,
 (RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def, assert_mode_def,errorT_def,untouched_def]));



val keep_mode_lem = store_thm(
    "keep_mode_lem",
    ``!m f s s' x. 
      (ARM_MODE s = m)        ==>
      (f s = ValueState x s') ==>
      (s.psrs = s'.psrs)
     ==> 
      (ARM_MODE s' = m)``,
     NTAC 5 STRIP_TAC THEN EVAL_TAC THEN METIS_TAC []);



val untouched_av_on_coprocessor_update_lem = store_thm(
     "untouched_av_on_coprocessor_update_lem",
     ``!s gst. (mmu_requirements s gst) ==>
       (access_violation s =
        access_violation ((arm_state_coprocessors_fupd 
(Coprocessors_state_fupd (coproc_state_cp15_fupd (\cp15. cp15 with <| 
SCR := scr |>)))) s))``,
     (NTAC 2 STRIP_TAC)
        THEN (`mmu_requirements ( (arm_state_coprocessors_fupd 
(Coprocessors_state_fupd (coproc_state_cp15_fupd (\cp15. cp15 with <| 
SCR := scr |>)))) s) gst = mmu_requirements s gst` by RW_TAC 
(srw_ss()) [mmu_requirements_def])
        THEN REPEAT STRIP_TAC
        THEN RES_TAC
        THEN IMP_RES_TAC access_violation_req
        THEN RW_TAC (srw_ss()) [access_violation_pure_def]);







val preserve_relation_comb_16_27_thm = store_thm(
    "preserve_relation_comb_16_27_thm",
    ``(preserve_relation_mmu G (assert_mode 16w) (assert_mode 16w) f y) ==> (preserve_relation_mmu G (assert_mode 16w) (comb_mode 16w 27w) f y)``,
    `comb (assert_mode 16w) (assert_mode 27w) (comb_mode 16w 27w)` by (RW_TAC (srw_ss()) [ comb_mode_def, comb_def] THEN METIS_TAC [])
      THEN RW_TAC (srw_ss()) [preserve_relation_comb_thm1, comb_mode_def, comb_def]
      THEN IMP_RES_TAC preserve_relation_comb_thm1);




(* Extras *)


val empty_unt_def = Define `empty_unt (g:word32) (s1:arm_state) (s2:arm_state) = T`;
val empty_sim_def = Define `empty_sim (g:word32) (s1:arm_state) (s2:arm_state) = T`;


val strict_unt_def = Define `strict_unt (g:word32) s t =    (s.psrs         = t.psrs)
                                                         /\ (s.registers    = t.registers)
                                                         /\ (s.memory       = t.memory)
                                                         /\ (s.coprocessors = t.coprocessors)
                                                         /\ (s.information  = t.information)`;


val reflex_priv_mode_similar_thm = store_thm(
    "reflex_priv_mode_similar_thm",
    ``refl_rel priv_mode_similar``,
    RW_TAC (srw_ss()) [refl_rel_def,priv_mode_similar_def] THEN RW_TAC (srw_ss()) []);


val reflex_priv_mode_constraints_thm = store_thm("reflex_priv_mode_constraints_thm",
              `` reflexive_comp  priv_mode_constraints (assert_mode 16w)``, 
                RW_TAC (srw_ss()) [reflexive_comp_def,priv_mode_constraints_def,assert_mode_def]);

val reflex_priv_mode_constraints_v2_thm = store_thm("reflex_priv_mode_constraints_v2_thm",
              `` reflexive_comp  priv_mode_constraints_v2 (assert_mode 16w)``, 
                RW_TAC (srw_ss()) [reflexive_comp_def,priv_mode_constraints_def, reflex_priv_mode_constraints_thm,priv_mode_constraints_v2_def,assert_mode_def]);



val trans_priv_mode_constraints_thm = 
    store_thm("trans_priv_mode_constraints_thm",
	      ``trans_fun priv_mode_constraints``,
	      RW_TAC let_ss [ trans_fun_def,priv_mode_constraints_def]
		     THEN RW_TAC (srw_ss()) [] THEN 
		     FULL_SIMP_TAC (srw_ss()) [get_base_vector_table_def,ARM_MODE_def,ARM_READ_CPSR_def]);
	
val reflex_priv_mode_similar_thm = store_thm(
    "reflex_priv_mode_similar_thm",
    ``refl_rel priv_mode_similar``,
    RW_TAC (srw_ss()) [refl_rel_def, priv_mode_similar_def] THEN RW_TAC (srw_ss()) []);


val generate_priv_mode_similar_lem = store_thm(
    "generate_priv_mode_similar_lem",
    ``!g s1 s2. (ARM_MODE s1 = 16w) ==> (ARM_MODE s2 = 16w) ==> (priv_mode_similar g s1 s2)``,
    RW_TAC (srw_ss()) [priv_mode_similar_def]);


val reflex_empty_sim_thm = store_thm(
    "reflex_empty_sim_thm",
    ``refl_rel empty_sim``,
    RW_TAC (srw_ss()) [refl_rel_def,empty_sim_def] THEN RW_TAC (srw_ss()) []);


val reflex_strict_unt_thm = store_thm(
   "reflex_strict_unt_thm",
   ``!u. reflexive_comp strict_unt (assert_mode u)``, 
   RW_TAC (srw_ss()) [reflexive_comp_def, strict_unt_def,assert_mode_def]);

val strict_unt_and_priv_mode_constraints_v2_lem = store_thm(
    "strict_unt_and_priv_mode_constraints_v2_lem",
    ``strict_unt g a b ==> priv_mode_constraints_v2 g b c ==>  priv_mode_constraints_v2 g a c``,
    RW_TAC (srw_ss()) [strict_unt_def, priv_mode_constraints_v2_def, priv_mode_constraints_v1_def, ARM_MODE_def, ARM_READ_CPSR_def, LET_DEF, vector_table_address_def, get_base_vector_table_def, get_pc_value_def] THEN FULL_SIMP_TAC (srw_ss()) []);

val trans_strict_unt_thm = 
    store_thm("trans_strict_unt_thm",
	      ``trans_fun strict_unt``,
	      RW_TAC let_ss [ trans_fun_def, strict_unt_def]
		     THEN RW_TAC (srw_ss()) [] );


val reflex_empty_unt_thm = store_thm(
   "reflex_empty_unt_thm",
   ``!u. reflexive_comp empty_unt (assert_mode u)``, 
   RW_TAC (srw_ss()) [reflexive_comp_def, empty_unt_def,assert_mode_def]);


val trans_empty_unt_thm = 
    store_thm("trans_empty_unt_thm",
	      ``trans_fun empty_unt``,
	      RW_TAC let_ss [ trans_fun_def, empty_unt_def]
		     THEN RW_TAC (srw_ss()) [] );

val strict_unt_lem = store_thm(
    "strict_unt_lem",
    ``! COMP.
        preserve_relation_mmu COMP (assert_mode u) (assert_mode u) strict_unt empty_sim
    ==> preserve_relation_mmu COMP (assert_mode u) (assert_mode u) empty_unt empty_sim``,
    RW_TAC (srw_ss()) [empty_unt_def, strict_unt_def, preserve_relation_mmu_def] 
      THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
      THEN METIS_TAC []);

val gen_strict_unt_lem = store_thm(
    "gen_strict_unt_lem",
    ``! COMP.
        (!u. preserve_relation_mmu COMP (assert_mode u) (assert_mode u) strict_unt empty_sim)
    ==> (!u. preserve_relation_mmu COMP (assert_mode u) (assert_mode u) empty_unt empty_sim)``,
    RW_TAC (srw_ss()) [empty_unt_def, strict_unt_def, preserve_relation_mmu_def] 
      THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
      THEN METIS_TAC []);


val empty_extras_lem = store_thm(
    "empty_extras_lem",
    ``! COMP.
       preserve_relation_mmu COMP (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar 
     = preserve_relation_mmu COMP (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim``,
    STRIP_TAC THEN EQ_TAC
      THENL[ RW_TAC (srw_ss()) [LET_DEF, preserve_relation_mmu_def, assert_mode_def, empty_unt_def, empty_sim_def]
                THEN `priv_mode_similar g s1 s2` by FULL_SIMP_TAC (srw_ss()) [similar_def, priv_mode_similar_def]
                THEN METIS_TAC [],
             RW_TAC (srw_ss()) [LET_DEF, preserve_relation_mmu_def, assert_mode_def, empty_unt_def, empty_sim_def]
                THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
                THEN NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (srw_ss()) [priv_mode_similar_def, untouched_def, LET_DEF, priv_mode_constraints_def])]);



val fixed_flags_def = Define `fixed_flags xI xF g s1 s2 = (((ARM_MODE s1 = 16w) ==> ((s1.psrs(0,CPSR)).I = xI)) /\ ((s1.psrs(0,CPSR)).F = xF) /\ ((ARM_MODE s2 = 16w) ==> ((s2.psrs(0,CPSR)).I = xI)) /\ ((s2.psrs(0,CPSR)).F = xF)) `;


val fixed_flags_empty_lem = store_thm(
    "fixed_flags_empty_lem",
    ``!COMP inv1 inv2 uf.
      ((!xI xF. preserve_relation_mmu COMP (assert_mode 16w) inv2 uf (fixed_flags xI xF) )
              = preserve_relation_mmu COMP (assert_mode 16w) inv2 uf empty_sim)
      /\
      ((!xI xF. preserve_relation_mmu COMP inv1 inv2 uf (fixed_flags xI xF) )
            ==> preserve_relation_mmu COMP inv1 inv2 uf empty_sim)``,
    NTAC 5 STRIP_TAC
       THENL[ EQ_TAC
                THENL[ RW_TAC (srw_ss()) [preserve_relation_mmu_def, fixed_flags_def, empty_sim_def]
                          THEN SPEC_ASSUM_TAC (``!xI g s1 s2. X``, [``(((s1:arm_state).psrs(0,CPSR)):ARMpsr).I``, ``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
                          THEN ` ((s2.psrs (0,CPSR)).I ⇔ (s1.psrs (0,CPSR)).I) ∧ ((s2.psrs (0,CPSR)).F ⇔ (s1.psrs (0,CPSR)).F)` by FULL_SIMP_TAC (srw_ss()) [similar_def]
                          THEN UNDISCH_ALL_TAC
                          THEN RW_TAC (srw_ss()) []
                          THEN Cases_on `ARM_MODE s2 = 16w` 
                          THEN FULL_SIMP_TAC (srw_ss()) [],
                       RW_TAC (srw_ss()) [preserve_relation_mmu_def, fixed_flags_def, empty_sim_def]
                          THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
                          THEN NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [assert_mode_def])
                          THEN METIS_TAC [untouched_def]],
              RW_TAC (srw_ss()) [preserve_relation_mmu_def, fixed_flags_def, empty_sim_def]
                THEN SPEC_ASSUM_TAC (``!xI g s1 s2. X``, [``(((s1:arm_state).psrs(0,CPSR)):ARMpsr).I``, ``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
                THEN ` ((s2.psrs (0,CPSR)).I ⇔ (s1.psrs (0,CPSR)).I) ∧ ((s2.psrs (0,CPSR)).F ⇔ (s1.psrs (0,CPSR)).F)` by FULL_SIMP_TAC (srw_ss()) [similar_def]
                THEN UNDISCH_ALL_TAC 
                THEN RW_TAC (srw_ss()) []
                THEN Cases_on `ARM_MODE s2 = 16w`
                THEN FULL_SIMP_TAC (srw_ss()) []]);


val fix_flags_def = Define `fix_flags xI xF uy g s1 s2 =  ((uy g s1 s2) /\ (fixed_flags xI xF g s1 s2))`;


val fix_flags_lem = store_thm(
    "fix_flags_lem",
    ``!COMP inv1 inv2 uf uy.
      ((!xI xF. preserve_relation_mmu COMP (assert_mode 16w) inv2 uf (fix_flags xI xF uy) )
              = preserve_relation_mmu COMP (assert_mode 16w) inv2 uf uy)
      /\
      ((!xI xF. preserve_relation_mmu COMP inv1 inv2 uf (fix_flags xI xF uy) )
            ==> preserve_relation_mmu COMP inv1 inv2 uf uy)``,
    NTAC 6 STRIP_TAC
       THENL[ EQ_TAC
                THENL[ RW_TAC (srw_ss()) [preserve_relation_mmu_def, fixed_flags_def, fix_flags_def]
                          THEN SPEC_ASSUM_TAC (``!xI g s1 s2. X``, [``(((s1:arm_state).psrs(0,CPSR)):ARMpsr).I``, ``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
                          THEN ` ((s2.psrs (0,CPSR)).I ⇔ (s1.psrs (0,CPSR)).I) ∧ ((s2.psrs (0,CPSR)).F ⇔ (s1.psrs (0,CPSR)).F)` by FULL_SIMP_TAC (srw_ss()) [similar_def]
                          THEN UNDISCH_ALL_TAC
                          THEN RW_TAC (srw_ss()) []
                          THEN Cases_on `ARM_MODE s2 = 16w` 
                          THEN FULL_SIMP_TAC (srw_ss()) [],
                       RW_TAC (srw_ss()) [preserve_relation_mmu_def, fixed_flags_def, fix_flags_def]
                          THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
                          THEN NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [assert_mode_def])
                          THEN METIS_TAC [untouched_def]],
              RW_TAC (srw_ss()) [preserve_relation_mmu_def, fixed_flags_def, fix_flags_def]
                THEN SPEC_ASSUM_TAC (``!xI g s1 s2. X``, [``(((s1:arm_state).psrs(0,CPSR)):ARMpsr).I``, ``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
                THEN ` ((s2.psrs (0,CPSR)).I ⇔ (s1.psrs (0,CPSR)).I) ∧ ((s2.psrs (0,CPSR)).F ⇔ (s1.psrs (0,CPSR)).F)` by FULL_SIMP_TAC (srw_ss()) [similar_def]
                THEN UNDISCH_ALL_TAC 
                THEN RW_TAC (srw_ss()) []
                THEN Cases_on `ARM_MODE s2 = 16w`
                THEN FULL_SIMP_TAC (srw_ss()) []]);


val extras_lem = store_thm(
    "extras_lem",
    ``!A. (!u. preserve_relation_mmu (A) (assert_mode u) (assert_mode u) empty_unt empty_sim) ==>
             ((preserve_relation_mmu (A) (assert_mode u) (assert_mode u) empty_unt empty_sim)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints (fix_flags xI xF priv_mode_similar))
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim))
)``,
    RW_TAC (srw_ss()) [empty_extras_lem, fix_flags_lem] THEN METIS_TAC [empty_extras_lem, fix_flags_lem]);




val extras_lem2 = store_thm(
    "extras_lem2",
    ``!A.     (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim) ==>
             ((preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints (fix_flags xI xF priv_mode_similar))
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)))``,
    RW_TAC (srw_ss()) [empty_extras_lem, fix_flags_lem] THEN METIS_TAC [empty_extras_lem, fix_flags_lem]);




val extras_lem3 = store_thm(
    "extras_lem3",
    ``!A. (!u. preserve_relation_mmu (A) (assert_mode u) (assert_mode u) strict_unt empty_sim) ==>
             ((preserve_relation_mmu (A) (assert_mode u) (assert_mode u) empty_unt empty_sim)
           /\ (preserve_relation_mmu (A) (assert_mode u) (assert_mode u) strict_unt empty_sim)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints (fix_flags xI xF priv_mode_similar))
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)))``, 
    RW_TAC (srw_ss()) [gen_strict_unt_lem, empty_extras_lem, fix_flags_lem] THEN METIS_TAC [gen_strict_unt_lem, empty_extras_lem, fix_flags_lem]);




val extras_lem4 = store_thm(
    "extras_lem4",
    ``!A.     (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) strict_unt empty_sim) ==>
             ((preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) strict_unt empty_sim)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar)
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints (fix_flags xI xF priv_mode_similar))
           /\ (preserve_relation_mmu (A) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)))``,
    RW_TAC (srw_ss()) [strict_unt_lem, empty_extras_lem, fix_flags_lem] THEN METIS_TAC [strict_unt_lem, empty_extras_lem, fix_flags_lem]);








 val comb_monot_thm = store_thm("comb_monot_thm", 
	       ``!a:(arm_state -> bool). comb a a a``,  
	       RW_TAC (srw_ss()) [comb_def]); 



val preserve_relation_comb_thm = 
    store_thm ("preserve_relation_comb_thm", 
	       ``! a b c d f  uf uy.  
	      preserve_relation_mmu  f d b uf uy 
	      ==> 
	      comb a b c ==> 
	      preserve_relation_mmu  f d c uf uy``, 
	       RW_TAC (srw_ss()) [preserve_relation_mmu_def,comb_def]  
		      THEN PAT_ASSUM ``∀g s1 s2. X``  
		      (fn thm => ASSUME_TAC (SPECL [``g:bool[32]``, 
						    ``s1:arm_state``, ``s2:arm_state``] thm)) 
    THEN RES_TAC 
	 THEN RW_TAC (srw_ss()) []);  



val global_aligned_word_readable_lem = store_thm(
    "global_aligned_word_readable_lem",
    ``mmu_requirements s1 g  ==>
      mmu_requirements s2 g  ==>
      (aligned_word_readable s1 is_thumb add =  aligned_word_readable s2 is_thumb add)``,
     RW_TAC (srw_ss()) [aligned_word_readable_def]
       THEN (NTAC 2 RES_TAC)
       THEN IMP_RES_TAC mmu_requirements_simp
       THEN IMP_RES_TAC same_setup_same_rights_lem
       THEN METIS_TAC [same_setup_same_rights_lem]);

























val seqT_preserves_relation_comb_thm =
    store_thm ("seqT_preserves_relation_comb_thm",
    ``! f1 f2 k inv2 comb_inv  uf uy.
          (comb  (assert_mode k) inv2 comb_inv) ==>
	  (trans_fun uf) ==>
          (preserve_relation_mmu  f1 (assert_mode k) (assert_mode k) uf uy)       ==>
          (preserve_relation_mmu_abs  f2 (assert_mode k) (comb_inv) uf uy) ==>
          (preserve_relation_mmu  (f1 >>= (f2)) (assert_mode k) comb_inv uf uy)
``,
    (RW_TAC (srw_ss()) [seqT_def,constT_def,preserve_relation_mmu_def,preserve_relation_mmu_abs_def,trans_fun_def]) 
    THEN (UNDISCH_ALL_TAC
       THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) []))
    THENL [UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
THEN RES_TAC
THEN IMP_RES_TAC untouched_trans
       THEN FULL_SIMP_TAC (srw_ss()) []
THEN METIS_TAC [untouched_trans, comb_rel_lem],
RW_TAC (srw_ss()) []
THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
       THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN Cases_on `assert_mode k s2`
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def])
       THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (srw_ss()) [assert_mode_def,comb_def]
THEN Cases_on `f2 a b`
THEN Cases_on `f2 a' b'`
THEN (NTAC 2 (RES_TAC
THEN IMP_RES_TAC untouched_trans
       THEN FULL_SIMP_TAC (srw_ss()) []
THEN IMP_RES_TAC untouched_mmu_setup_lem
THEN
TRY (PAT_ASSUM ``!c g' s1'' s2''. X`` (fn th => ASSUME_TAC (SPECL [``a:'a``, ``g:bool[32]``, ``b:arm_state``, ``b':arm_state``] th)))
THEN
(TRY (PAT_ASSUM `` ∀g st1 st2 st3. X`` (fn th => ASSUME_TAC (SPECL [ ``g:bool[32]``, ``s1:arm_state``, ``b:arm_state``, ``b'':arm_state``] th) THEN ASSUME_TAC (SPECL [ ``g:bool[32]``, ``s2:arm_state``, ``b':arm_state``, ``b''':arm_state``] th))))
 THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) [])),
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN Cases_on `assert_mode k s2`
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [],
RW_TAC (srw_ss()) []
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []]);

