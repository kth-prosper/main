
val IT_advance_constlem = store_thm(
    "IT_advance_constlem",
    ``((s.psrs(0,CPSR)).IT = 0w) ==> (((IT_advance <|proc :=0|>) s) = (ValueState () s))``,
    EVAL_TAC
      THEN RW_TAC (srw_ss()) []
      THENL [`!(x:unit). x = ()` by (Cases_on `x` THEN EVAL_TAC)
                THEN SPEC_ASSUM_TAC (``!x. X``, [``ARB:unit``])
                THEN FULL_SIMP_TAC (srw_ss()) [],
             ALL_TAC,
             ALL_TAC]
      THEN UNDISCH_ALL_TAC 
      THEN EVAL_TAC
      THEN RW_TAC (srw_ss()) []
      THEN Cases_on `s`
      THEN FULL_SIMP_TAC (srw_ss()) [arm_state_psrs_fupd]
      THEN `((0,CPSR) =+ f0 (0,CPSR) with IT := ((f0 (0,CPSR)).IT)) f0 = f0` by FULL_SIMP_TAC (srw_ss()) [psrs_update_in_update_thm]
      THEN Q.ABBREV_TAC `x = (f0 (0,CPSR)).IT`
      THEN  RW_TAC (srw_ss()) [arm_state_psrs_fupd]);


val condition_passed_constlem = store_thm(
    "condition_passed_constlem",
    ``!s cond. ?x. (condition_passed <|proc:=0|> cond) s = ValueState x s``,
    EVAL_TAC THEN RW_TAC (srw_ss()) [] THEN RW_TAC (srw_ss()) []);

val condition_passed_similar_lem = store_thm(
    "condition_passed_similar_lem",
    ``!s1 s2 cond. (similar g s1 s2) ==> (?pass. (((condition_passed <|proc:=0|> cond) s1 = ValueState pass s1) /\ ((condition_passed <|proc:=0|> cond) s2 = ValueState pass s2)))``,
    RW_TAC (srw_ss()) []
      THEN IMP_RES_TAC  similarity_implies_equal_av_thm
      THEN UNDISCH_TAC ``similar g s1 s2``
      THEN EVAL_TAC THEN RW_TAC (srw_ss()) [] THEN RW_TAC (srw_ss()) []);


val arm_instr_core_def = Define `arm_instr_core ii (pass:bool) (enc:Encoding) (cond:word4) (inst:ARMinstruction) =
   if pass then
           case inst of
              Unpredictable -> errorT "decode: unpredictable"
           || Undefined -> take_undef_instr_exception ii
           || Branch b -> branch_instruction ii (enc,b)
           || DataProcessing d -> data_processing_instruction ii (enc,d)
           || StatusAccess s -> status_access_instruction ii (enc,s)
           || LoadStore l -> load_store_instruction ii (enc,l)
           || Miscellaneous m -> miscellaneous_instruction ii (enc,m)
           || Coprocessor c -> coprocessor_instruction ii (enc,cond,c)
         else
           increment_pc ii enc`;



g `preserve_relation_mmu (arm_instr_core <|proc:=0|> pass enc cond inst) (assert_mode 16w) mode_mix priv_mode_constraints_v2 priv_mode_similar`;
e(RW_TAC (srw_ss()) [arm_instr_core_def]);
e(CASE_TAC);
(* 8 cases *)
(* error *)
e(MODE_MIX_TAC ``assert_mode 16w``);
go_on 1;
(* take undef instr exception *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
e(FULL_SIMP_TAC (srw_ss()) [take_undef_instr_exception_comb_thm]);
(* branch instruction *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
e(FULL_SIMP_TAC (srw_ss()) [branch_instruction_comb_thm]);
(* data processing instruction *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
e(FULL_SIMP_TAC (srw_ss()) [data_processing_instruction_comb_thm]);
(* status access instruction *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
e(FULL_SIMP_TAC (srw_ss()) [status_access_instruction_comb_thm]);
(* load store instruction *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
e(FULL_SIMP_TAC (srw_ss()) [load_store_instruction_comb_thm]);
(* misc instruction *)
e(FULL_SIMP_TAC (srw_ss()) [miscellaneous_instruction_comb_thm]);
(* coprocessor instruction *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
e(FULL_SIMP_TAC (srw_ss()) [coprocessor_instruction_comb_thm]);
(* increment PC *)
e(MODE_MIX_TAC ``assert_mode 16w``);
e(FULL_SIMP_TAC (srw_ss()) [increment_pc_thm]);
val arm_instr_core_comb_thm = save_comb_thm("arm_instr_core_comb_thm", top_thm(), ``arm_instr_core``);


val arm_instr_alternative_def = store_thm(
    "arm_instr_alternative_def",
    ``arm_instr ii (enc,cond,inst) =
    (condition_passed ii cond >>=
      (λpass.
         arm_instr_core ii pass enc cond inst)) >>=
     (λu.
        condT
          (case inst of
              Unpredictable -> T
           || Undefined -> T
           || Branch v6 -> T
           || DataProcessing v7 -> T
           || StatusAccess v8 -> T
           || LoadStore v9 -> T
           || Miscellaneous (Hint v33) -> T
           || Miscellaneous (Breakpoint v34) -> T
           || Miscellaneous (Data_Memory_Barrier v35) -> T
           || Miscellaneous (Data_Synchronization_Barrier v36) -> T
           || Miscellaneous (Instruction_Synchronization_Barrier v37) ->
                T
           || Miscellaneous (Swap v38 v39 v40 v41) -> T
           || Miscellaneous (Preload_Data v42 v43 v44 v45) -> T
           || Miscellaneous (Preload_Instruction v46 v47 v48) -> T
           || Miscellaneous (Supervisor_Call v49) -> T
           || Miscellaneous (Secure_Monitor_Call v50) -> T
           || Miscellaneous (Enterx_Leavex v51) -> T
           || Miscellaneous Clear_Exclusive -> T
           || Miscellaneous (If_Then v52 v53) -> F
           || Coprocessor v11 -> T) (IT_advance ii))``,
     RW_TAC (srw_ss()) [arm_instr_core_def, arm_instr_def]);


val arm_instr_comb_thm = store_thm("arm_instr_comb_thm",
    ``preserve_relation_mmu (arm_instr <|proc:=0|> (enc, cond, inst)) (assert_mode 16w) mode_mix priv_mode_constraints_v2 priv_mode_similar``,
    RW_TAC (srw_ss()) [arm_instr_alternative_def, preserve_relation_mmu_def, seqT_def, condT_def]
       THEN (ASSUME_TAC (SPECL [``s1:arm_state``, ``s2:arm_state``, ``cond:word4``] condition_passed_similar_lem)
                THEN NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [untouched_refl])
                THEN ASSUME_TAC reflex_priv_mode_constraints_v2_thm 
                THEN IMP_RES_TAC reflexive_comp_def 
                THEN UNDISCH_ALL_TAC 
                THEN RW_TAC (srw_ss()) []
                THENL [FULL_SIMP_TAC (srw_ss()) [mode_mix_def, assert_mode_def],
                       FULL_SIMP_TAC (srw_ss()) [mode_mix_def, assert_mode_def],
                       IMP_RES_TAC similarity_implies_equal_av_thm, 
                       IMP_RES_TAC similarity_implies_equal_av_thm, 
                       ALL_TAC]
                THEN Cases_on `arm_instr_core <|proc := 0|> pass enc cond inst s2`
                THEN ASSUME_TAC arm_instr_core_comb_thm
                THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]
                THEN UNDISCH_ALL_TAC 
                THEN RW_TAC (srw_ss()) []
                THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
                THEN UNDISCH_ALL_TAC 
                THEN RW_TAC (srw_ss()) [constT_def]
                THEN IMP_RES_TAC  similarity_implies_equal_av_thm
                THEN UNDISCH_ALL_TAC 
                THEN RW_TAC (srw_ss()) []
                THEN Cases_on `ARM_MODE s1' = 16w`
                THEN IMP_RES_TAC similarity_implies_equal_av_thm
                THEN IMP_RES_TAC similarity_implies_equal_mode_thm
                THEN FULL_SIMP_TAC (srw_ss()) [])
       THENL [ASSUME_TAC (CONJUNCT1 (CONJUNCT2 IT_advance_thm))
                THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, priv_mode_constraints_v2_def]
                THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1':arm_state``, ``b:arm_state``])
                THEN IMP_RES_TAC untouched_mmu_setup_lem
                THEN (NTAC 2 ((`(ARM_MODE s1' = 16w) /\ (ARM_MODE b = 16w)` by FULL_SIMP_TAC (srw_ss())  [])
                                  THEN FULL_SIMP_TAC (srw_ss()) []
                                  THEN RES_TAC 
                                  THEN FULL_SIMP_TAC (srw_ss()) []))
                THEN METIS_TAC [untouched_trans, trans_priv_mode_constraints_thm, trans_fun_def, mode_mix_def],
              `((s1'.psrs (0,CPSR)).IT = 0w) /\ ((b.psrs (0,CPSR)).IT = 0w)` by FULL_SIMP_TAC (srw_ss())  [priv_mode_constraints_v2_def, priv_mode_constraints_v1_def, LET_DEF]
                THEN IMP_RES_TAC IT_advance_constlem
                THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []]);





