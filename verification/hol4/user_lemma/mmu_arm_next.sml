(**************************************)
(****    minor state updates     ******)
(**************************************)

(* empty access list *)

val empty_accesses_av_lem = store_thm(
    "empty_accesses_av_lem",
    ``~(access_violation (s with accesses := []))``,
    ASSUME_TAC (SPEC ``(s with accesses := [])`` (GEN_ALL empty_accesses_full_lem))
      THEN ASSUME_TAC (SPECL [``(s with accesses := [])``, ``T``, ``F``, ``ARB:word32``] access_violation_def)
      THEN FULL_SIMP_TAC (srw_ss()) []);

val empty_accesses_requirements_lem = store_thm(
    "empty_accesses_requirements_lem",
    ``(mmu_requirements (s with accesses := []) g) = (mmu_requirements s g)``,
    RW_TAC (srw_ss()) [mmu_requirements_def]);

val empty_accesses_aligned_word_readable_lem = store_thm(
    "empty_accesses_aligned_word_readable_lem",
    ``(aligned_word_readable (s with accesses := []) ist g) = (aligned_word_readable s ist g)``,
    RW_TAC (srw_ss()) [aligned_word_readable_def]);

val empty_accesses_similar_lem = store_thm(
    "empty_accesses_similar_lem",
    `` (similar g s1 s2) ==> (similar g (s1 with accesses := []) (s2 with accesses := []))``,
    RW_TAC (srw_ss()) [similar_def, equal_user_register_def] THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_full_lem, access_violation_def]);

val empty_accesses_priv_mode_similar_lem = store_thm(
    "empty_accesses_priv_mode_similar_lem",
    ``(priv_mode_similar g (s1 with accesses := []) (s2 with accesses := [])) = (priv_mode_similar g s1 s2)``,
    RW_TAC (srw_ss()) [priv_mode_similar_def, LET_DEF, ARM_MODE_def, ARM_READ_CPSR_def]);

val empty_accesses_mode_lem = store_thm(
    "empty_accesses_mode_lem",
    ``(ARM_MODE (s with accesses := [])) = (ARM_MODE s)``,
    RW_TAC (srw_ss()) [ARM_MODE_def, ARM_READ_CPSR_def]);

val empty_accesses_untouched_lem = store_thm(
    "empty_accesses_untouched_lem",
    ``((untouched g (s with accesses := []) t) = (untouched g s t)) /\ ((untouched g s (t with accesses := [])) = (untouched g s t)) ``,
 STRIP_TAC THEN EQ_TAC THEN RW_TAC (srw_ss()) [untouched_def, LET_DEF, empty_accesses_mode_lem] THEN FULL_SIMP_TAC (srw_ss()) []);

val empty_accesses_strict_unt_lem = store_thm(
    "empty_accesses_strict_unt_lem",
    ``((strict_unt g (s with accesses := []) t) = (strict_unt g s t)) /\ ((strict_unt g s (t with accesses := [])) = (strict_unt g s t)) ``,
 STRIP_TAC THEN EQ_TAC THEN RW_TAC (srw_ss()) [strict_unt_def, LET_DEF, empty_accesses_mode_lem] THEN FULL_SIMP_TAC (srw_ss()) []);

val empty_accesses_priv_mode_constraints_v1_lem = store_thm(
    "empty_accesses_priv_mode_constraints_v1_lem",
    ``((priv_mode_constraints_v1 g (s with accesses := []) t) = (priv_mode_constraints_v1 g s t)) /\ ((priv_mode_constraints_v1 g s t) ==> (priv_mode_constraints_v1 g s (t with accesses := [])))``,
 STRIP_TAC THENL [EQ_TAC, ALL_TAC] THEN RW_TAC (srw_ss()) [priv_mode_constraints_v1_def, LET_DEF, empty_accesses_mode_lem, get_base_vector_table_def, empty_accesses_av_lem] THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_av_lem]);

val empty_accesses_priv_mode_constraints_v2_lem = store_thm(
    "empty_accesses_priv_mode_constraints_v2_lem",
    ``((priv_mode_constraints_v2 g (s with accesses := []) t) = (priv_mode_constraints_v2 g s t)) /\ ((priv_mode_constraints_v2 g s t) ==> (priv_mode_constraints_v2 g s (t with accesses := [])))``,
 STRIP_TAC THENL [EQ_TAC, ALL_TAC] THEN RW_TAC (srw_ss()) [priv_mode_constraints_v2_def, LET_DEF, empty_accesses_mode_lem, empty_accesses_priv_mode_constraints_v1_lem, get_pc_value_def] THEN FULL_SIMP_TAC (srw_ss()) []);

(* updated interrupt_wait *)

val updated_int_wait_mode_lem = store_thm(
    "updated_int_wait_mode_lem",
    ``(ARM_MODE (s with interrupt_wait updated_by IWU)) = (ARM_MODE s)``,
    RW_TAC (srw_ss()) [ARM_MODE_def, ARM_READ_CPSR_def]);

val updated_int_wait_untouched_lem = store_thm(
    "updated_int_wait_untouched_lem",
    ``(untouched g s (t with interrupt_wait updated_by IWU)) = (untouched g s t)``,
    EQ_TAC THEN RW_TAC (srw_ss()) [untouched_def, LET_DEF, updated_int_wait_mode_lem] THEN FULL_SIMP_TAC (srw_ss()) []);

val updated_int_wait_priv_mode_constraints_v2_lem = store_thm(
    "updated_int_wait_priv_mode_constraints_v2_lem",
    ``(mmu_requirements t g) ==> ((priv_mode_constraints_v2 g s (t with interrupt_wait updated_by IWU)) = (priv_mode_constraints_v2 g s t))``,
    STRIP_TAC THEN EQ_TAC THEN RW_TAC (srw_ss()) [get_base_vector_table_def, priv_mode_constraints_v2_def, get_pc_value_def, priv_mode_constraints_v1_def, LET_DEF, updated_int_wait_mode_lem, trivially_untouched_av_lem] THEN FULL_SIMP_TAC (srw_ss()) [] THEN MP_TAC (SPECL [``t:arm_state``, ``(t with interrupt_wait updated_by IWU):arm_state``, ``g:word32``] trivially_untouched_av_lem) THEN UNDISCH_MATCH_TAC ``~ access_violation X`` THEN UNDISCH_TAC ``mmu_requirements t g`` THEN RW_TAC (srw_ss()) []);

val updated_int_wait_priv_mode_similar_lem = store_thm(
    "updated_int_wait_priv_mode_similar_lem",
    ``(priv_mode_similar g (s1 with interrupt_wait updated_by IWU) (s2 with interrupt_wait updated_by IWU)) = (priv_mode_similar g s1 s2)``,
    RW_TAC (srw_ss()) [priv_mode_similar_def, LET_DEF, ARM_MODE_def, ARM_READ_CPSR_def]);

val updated_int_wait_similar_lem = store_thm(
    "updated_int_wait_similar_lem",
    ``(mmu_requirements s1 g) ==> (mmu_requirements s2 g) ==> (similar g s1 s2) ==> (similar g (s1 with interrupt_wait updated_by (0 =+ A)) (s2 with interrupt_wait updated_by (0 =+ A)))``,
    ASSUME_TAC (SPECL [``s1:arm_state``, ``(s1 with interrupt_wait updated_by (0 =+ A)):arm_state``, ``g:word32``] trivially_untouched_av_lem)
      THEN ASSUME_TAC (SPECL [``s2:arm_state``, ``(s2 with interrupt_wait updated_by (0 =+ A)):arm_state``, ``g:word32``] trivially_untouched_av_lem)
      THEN RW_TAC (srw_ss()) [similar_def, equal_user_register_def, updated_int_wait_mode_lem]
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN EVAL_TAC);



(**************************************)
(****      contract massaging    ******)
(**************************************)

val take_fiq_exception_comb_thm2 = store_thm(
    "take_fiq_exception_comb_thm2",
    ``preserve_relation_mmu (take_fiq_exception <|proc := 0|>) (assert_mode 16w) mode_mix  priv_mode_constraints_v2 priv_mode_similar``,
    MODE_MIX_TAC ``comb_mode 16w 17w`` THEN FULL_SIMP_TAC (srw_ss()) [take_fiq_exception_comb_thm]);

val take_irq_exception_comb_thm2 = store_thm(
    "take_irq_exception_comb_thm2",
    ``preserve_relation_mmu (take_irq_exception <|proc := 0|>) (assert_mode 16w) mode_mix  priv_mode_constraints_v2 priv_mode_similar``,
    MODE_MIX_TAC ``comb_mode 16w 18w`` THEN FULL_SIMP_TAC (srw_ss()) [take_irq_exception_comb_thm]);

val take_prefetch_abort_exception_comb_thm2 = store_thm(
    "take_prefetch_abort_exception_comb_thm2",
    ``preserve_relation_mmu (take_prefetch_abort_exception <|proc := 0|>) (assert_mode 16w) mode_mix priv_mode_constraints_v2 priv_mode_similar``,
    MODE_MIX_TAC ``comb_mode 16w 23w`` THEN FULL_SIMP_TAC (srw_ss()) [take_prefetch_abort_exception_comb_thm]);


(**************************************)
(****         main proof         ******)
(**************************************)



g` preserve_relation_mmu (mmu_arm_next irpt)
     (assert_mode 16w) mode_mix priv_mode_constraints_v2
     priv_mode_similar`;


e(Cases_on `irpt` THEN RW_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, mmu_arm_next_def]);

(* 1. instructions *)
e(FULL_SIMP_TAC (srw_ss()) [waiting_for_interrupt_def, readT_def]);
e(`s1.interrupt_wait 0 = s2.interrupt_wait 0` by FULL_SIMP_TAC (srw_ss()) [similar_def]);
e(Cases_on `s1.interrupt_wait 0` THEN FULL_SIMP_TAC (srw_ss()) []);

(* 1.1. waiting for any interrupt *)
e(ASSUME_TAC (SPECL [``g:word32``, ``s1:arm_state``] untouched_refl));
e(ASSUME_TAC (SPECL [``g:word32``, ``s2:arm_state``] untouched_refl));
e(ASSUME_TAC reflex_priv_mode_constraints_v2_thm);
e(FULL_SIMP_TAC (srw_ss()) [assert_mode_def, reflexive_comp_def]);
e(IMP_RES_TAC empty_accesses_similar_lem
THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_priv_mode_similar_lem, empty_accesses_mode_lem, mode_mix_def, empty_accesses_priv_mode_constraints_v2_lem, empty_accesses_untouched_lem]
THEN RES_TAC);

(* 1.2. not waiting for interrupt *)
e(ASSUME_TAC (CONJUNCT1 fetch_instruction_thm));
e(FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]);
e(SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1 with accesses:= []``, ``s2 with accesses := []``]));
e(IMP_RES_TAC empty_accesses_similar_lem
THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_priv_mode_similar_lem, empty_accesses_mode_lem, empty_accesses_untouched_lem, assert_mode_def, empty_sim_def]
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []);
e(Cases_on `a` THEN FULL_SIMP_TAC (srw_ss()) []);
e(ASSUME_TAC (SPECL [``g:word32``, ``s1':arm_state``, ``s2':arm_state``] generate_priv_mode_similar_lem));
e(ASSUME_TAC (SPECL [``g:word32``, ``s1':arm_state``, ``s2':arm_state``]  similarity_implies_equal_av_thm));
e(FULL_SIMP_TAC (srw_ss()) []);
e(RES_TAC);
e(Cases_on `access_violation s1'` THEN FULL_SIMP_TAC (srw_ss()) []);

(* 1.2.1. prefetch abort *)
e(IMP_RES_TAC untouched_mmu_setup_lem);
e(ASSUME_TAC take_prefetch_abort_exception_comb_thm2);
e(FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]);
e(SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1' with accesses:= []``, ``s2' with accesses := []``]));
e(IMP_RES_TAC empty_accesses_similar_lem
THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_priv_mode_similar_lem, empty_accesses_mode_lem, empty_accesses_untouched_lem, assert_mode_def, empty_accesses_priv_mode_similar_lem, empty_accesses_strict_unt_lem]
THEN RES_TAC
THEN IMP_RES_TAC untouched_trans
THEN IMP_RES_TAC (GEN_ALL strict_unt_and_priv_mode_constraints_v2_lem)
THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_priv_mode_constraints_v2_lem]);

(* 1.2.2. no prefetch abort *)
e(IMP_RES_TAC untouched_mmu_setup_lem);
e(Cases_on `r` THEN Cases_on `r'`);
e(ASSUME_TAC (SPECL [``r:ARMinstruction``, ``q':Encoding``, ``q'':word4``] (GEN_ALL arm_instr_comb_thm)));
e(FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]);
e(SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1' with accesses:= []``, ``s2' with accesses := []``]));
e(IMP_RES_TAC empty_accesses_similar_lem
THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_priv_mode_similar_lem, empty_accesses_mode_lem, empty_accesses_untouched_lem, assert_mode_def, empty_accesses_priv_mode_similar_lem, empty_accesses_strict_unt_lem]
THEN RES_TAC
THEN IMP_RES_TAC untouched_trans
THEN IMP_RES_TAC (GEN_ALL strict_unt_and_priv_mode_constraints_v2_lem)
THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_priv_mode_constraints_v2_lem]);
e(ASSUME_TAC (SPECL [``g:word32``, ``s1'':arm_state``, ``s2'':arm_state``]  similarity_implies_equal_av_thm));
e(FULL_SIMP_TAC (srw_ss()) []);
e(RES_TAC);
e(Cases_on `access_violation s1''` THEN FULL_SIMP_TAC (srw_ss()) []);

(* data abort *)
e(`(ARM_MODE s1'' = 16w) /\ (ARM_MODE s2'' = 16w)` by (UNDISCH_TAC ``priv_mode_constraints_v2 g s1' s1''`` THEN UNDISCH_TAC ``priv_mode_constraints_v2 g s2' s2''`` THEN RW_TAC (srw_ss()) [LET_DEF, priv_mode_constraints_v2_def, priv_mode_constraints_v1_def]));
e(IMP_RES_TAC untouched_mmu_setup_lem);
e(ASSUME_TAC take_data_abort_exception_comb_thm);
e(FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]);
e(SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1'' with accesses:= []``, ``s2'' with accesses := []``]));
e(IMP_RES_TAC empty_accesses_similar_lem
THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_priv_mode_similar_lem, empty_accesses_mode_lem, empty_accesses_untouched_lem, assert_mode_def, empty_accesses_priv_mode_similar_lem, empty_accesses_strict_unt_lem, priv_mode_constraints_v2_def, comb_mode_def, assert_mode_def, mode_mix_def, empty_accesses_priv_mode_constraints_v1_lem, empty_accesses_priv_mode_constraints_v2_lem]
THEN RES_TAC
THEN IMP_RES_TAC untouched_trans
THEN IMP_RES_TAC (SIMP_RULE (srw_ss()) [trans_fun_def] trans_priv_mode_constraints_thm)
THEN RES_TAC
THEN IMP_RES_TAC untouched_trans
THEN IMP_RES_TAC (SIMP_RULE (srw_ss()) [trans_fun_def] trans_priv_mode_constraints_thm)
THEN FULL_SIMP_TAC (srw_ss()) []);

(* 2. reset *)
e(FULL_SIMP_TAC (srw_ss()) [clear_wait_for_interrupt_def, writeT_def, seqT_def]);
e(Cases_on `take_reset <|proc := 0|> (s1 with accesses := [])` THEN Cases_on `take_reset <|proc := 0|> (s2 with accesses := [])` THEN ASSUME_TAC take_reset_comb_thm THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, comb_mode_def] THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``(s1 with accesses := []):arm_state``, ``(s2 with accesses := []):arm_state``])
THEN IMP_RES_TAC empty_accesses_similar_lem
THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_priv_mode_similar_lem, empty_accesses_mode_lem, mode_mix_def, empty_accesses_priv_mode_constraints_v2_lem, empty_accesses_untouched_lem]
THEN RES_TAC
THEN `ARB:unit = ()` by (Cases_on `(ARB:unit)` THEN FULL_SIMP_TAC (srw_ss()) [])
THEN FULL_SIMP_TAC (srw_ss()) [updated_int_wait_untouched_lem, updated_int_wait_mode_lem, updated_int_wait_priv_mode_constraints_v2_lem]
THEN IMP_RES_TAC untouched_mmu_setup_lem
THEN IMP_RES_TAC updated_int_wait_similar_lem
THEN IMP_RES_TAC (GEN_ALL updated_int_wait_priv_mode_similar_lem)
THEN IMP_RES_TAC similarity_implies_equal_av_thm
THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [updated_int_wait_untouched_lem, updated_int_wait_mode_lem, updated_int_wait_priv_mode_constraints_v2_lem, untouched_mmu_setup_lem, updated_int_wait_similar_lem]);


(* 3. irq *)
e(FULL_SIMP_TAC (srw_ss()) [clear_wait_for_interrupt_def, writeT_def, seqT_def]);
e(Cases_on `take_irq_exception <|proc := 0|> (s1 with accesses := [])` THEN Cases_on `take_irq_exception <|proc := 0|> (s2 with accesses := [])` THEN ASSUME_TAC take_irq_exception_comb_thm2 THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, comb_mode_def] THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``(s1 with accesses := []):arm_state``, ``(s2 with accesses := []):arm_state``])
THEN IMP_RES_TAC empty_accesses_similar_lem
THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_priv_mode_similar_lem, empty_accesses_mode_lem, mode_mix_def, empty_accesses_priv_mode_constraints_v2_lem, empty_accesses_untouched_lem]
THEN RES_TAC
THEN `ARB:unit = ()` by (Cases_on `(ARB:unit)` THEN FULL_SIMP_TAC (srw_ss()) [])
THEN FULL_SIMP_TAC (srw_ss()) [updated_int_wait_untouched_lem, updated_int_wait_mode_lem, updated_int_wait_priv_mode_constraints_v2_lem]
THEN IMP_RES_TAC untouched_mmu_setup_lem
THEN IMP_RES_TAC updated_int_wait_similar_lem
THEN IMP_RES_TAC (GEN_ALL updated_int_wait_priv_mode_similar_lem)
THEN IMP_RES_TAC similarity_implies_equal_av_thm
THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [updated_int_wait_untouched_lem, updated_int_wait_mode_lem, updated_int_wait_priv_mode_constraints_v2_lem, untouched_mmu_setup_lem, updated_int_wait_similar_lem]);




(* 4. fiq *)
e(FULL_SIMP_TAC (srw_ss()) [clear_wait_for_interrupt_def, writeT_def, seqT_def]);
e(Cases_on `take_fiq_exception <|proc := 0|> (s1 with accesses := [])` THEN Cases_on `take_fiq_exception <|proc := 0|> (s2 with accesses := [])` THEN ASSUME_TAC take_fiq_exception_comb_thm2 THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, comb_mode_def] THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``(s1 with accesses := []):arm_state``, ``(s2 with accesses := []):arm_state``])
THEN IMP_RES_TAC empty_accesses_similar_lem
THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_priv_mode_similar_lem, empty_accesses_mode_lem, mode_mix_def, empty_accesses_priv_mode_constraints_v2_lem, empty_accesses_untouched_lem]
THEN RES_TAC
THEN `ARB:unit = ()` by (Cases_on `(ARB:unit)` THEN FULL_SIMP_TAC (srw_ss()) [])
THEN FULL_SIMP_TAC (srw_ss()) [updated_int_wait_untouched_lem, updated_int_wait_mode_lem, updated_int_wait_priv_mode_constraints_v2_lem]
THEN IMP_RES_TAC untouched_mmu_setup_lem
THEN IMP_RES_TAC updated_int_wait_similar_lem
THEN IMP_RES_TAC (GEN_ALL updated_int_wait_priv_mode_similar_lem)
THEN IMP_RES_TAC similarity_implies_equal_av_thm
THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [updated_int_wait_untouched_lem, updated_int_wait_mode_lem, updated_int_wait_priv_mode_constraints_v2_lem, untouched_mmu_setup_lem, updated_int_wait_similar_lem]);

val mmu_arm_next_thm = top_thm();



