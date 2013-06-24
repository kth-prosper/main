;

val branch_to_empty_thm = store_thm(
    "branch_to_empty_thm",
    ``!u. preserve_relation_mmu (branch_to <|proc:=0|> add) (assert_mode u) (assert_mode u) empty_unt empty_sim``,
    RW_TAC (srw_ss()) [branch_to_def, write__reg_def, writeT_def, preserve_relation_mmu_def, untouched_def, assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def, similar_def, equal_user_register_def, empty_unt_def, empty_sim_def]
     THEN (TRY ((`reg <> RName_PC` by (Q.UNABBREV_TAC `user_regs` THEN FULL_SIMP_TAC (srw_ss()) []))))
     THEN (TRY (UNDISCH_TAC ``(reg:RName) <> RName_PC``))
     THEN EVAL_TAC
     THEN RW_TAC (srw_ss()) []
     THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``s1 with registers updated_by ((0,RName_PC) =+ add)``, ``g:word32``] trivially_untouched_av_lem)
     THEN ASSUME_TAC (SPECL [``s2:arm_state``, ``s2 with registers updated_by ((0,RName_PC) =+ add)``, ``g:word32``] trivially_untouched_av_lem)
     THEN FULL_SIMP_TAC (srw_ss()) []
     THEN RES_TAC
     THEN FULL_SIMP_TAC (srw_ss()) []);
val branch_to_thm = save_thm("branch_to_thm", MATCH_MP extras_lem branch_to_empty_thm);



val write_monitor_empty_thm = store_thm(
    "write_monitor_empty_thm",
    ``!u. preserve_relation_mmu (write_monitor <|proc:=0|> vl) (assert_mode u) (assert_mode u) empty_unt empty_sim``,
    RW_TAC (srw_ss()) [write_monitor_def, writeT_def, preserve_relation_mmu_def, untouched_def, assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def, similar_def, equal_user_register_def, empty_unt_def, empty_sim_def] 
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``s1 with monitors := (vl:ExclusiveMonitors)``, ``g:word32``] trivially_untouched_av_lem)
      THEN ASSUME_TAC (SPECL [``s2:arm_state``, ``s2 with monitors := (vl:ExclusiveMonitors)``, ``g:word32``] trivially_untouched_av_lem)
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN RES_TAC
      THEN FULL_SIMP_TAC (srw_ss()) []);
val write_monitor_thm = save_thm("write_monitor_thm", MATCH_MP extras_lem write_monitor_empty_thm);


val clear_event_register_empty_thm = store_thm(
    "clear_event_register_empty_thm",
    ``!u. preserve_relation_mmu (clear_event_register <|proc:=0|>) (assert_mode u) (assert_mode u) empty_unt empty_sim``,
    RW_TAC (srw_ss()) [clear_event_register_def, writeT_def, preserve_relation_mmu_def, untouched_def, assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def, similar_def, equal_user_register_def, empty_unt_def, empty_sim_def] 
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``s1 with event_register updated_by (0=+ F)``, ``g:word32``] trivially_untouched_av_lem)
      THEN ASSUME_TAC (SPECL [``s2:arm_state``, ``s2 with event_register updated_by (0=+ F)``, ``g:word32``] trivially_untouched_av_lem)
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN RES_TAC
      THEN FULL_SIMP_TAC (srw_ss()) []);
val clear_event_register_thm = save_thm("clear_event_register_thm", MATCH_MP extras_lem clear_event_register_empty_thm);



val wait_for_interrupt_empty_thm = store_thm(
    "wait_for_interrupt_empty_thm",
    ``!u. preserve_relation_mmu (wait_for_interrupt <|proc:=0|>) (assert_mode u) (assert_mode u) empty_unt empty_sim``,
    RW_TAC (srw_ss()) [wait_for_interrupt_def, writeT_def, preserve_relation_mmu_def, untouched_def, assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def, similar_def, equal_user_register_def, empty_unt_def, empty_sim_def] 
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``s1 with interrupt_wait updated_by (0=+ T)``, ``g:word32``] trivially_untouched_av_lem)
      THEN ASSUME_TAC (SPECL [``s2:arm_state``, ``s2 with interrupt_wait updated_by (0=+ T)``, ``g:word32``] trivially_untouched_av_lem)
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN RES_TAC
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN EVAL_TAC);
val wait_for_interrupt_thm = save_thm("wait_for_interrupt_thm", MATCH_MP extras_lem wait_for_interrupt_empty_thm);



val send_event_empty_thm = store_thm(
    "send_event_empty_thm",
    ``!u. preserve_relation_mmu (send_event <|proc:=0|>) (assert_mode u) (assert_mode u) empty_unt empty_sim``,
    RW_TAC (srw_ss()) [send_event_def, writeT_def, preserve_relation_mmu_def, untouched_def, assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def, similar_def, equal_user_register_def, empty_unt_def, empty_sim_def] 
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``s1 with event_register := K T``, ``g:word32``] trivially_untouched_av_lem)
      THEN ASSUME_TAC (SPECL [``s2:arm_state``, ``s2 with event_register := K T``, ``g:word32``] trivially_untouched_av_lem)
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN RES_TAC
      THEN FULL_SIMP_TAC (srw_ss()) []);
val send_event_thm = save_thm("send_event_thm", MATCH_MP extras_lem send_event_empty_thm);



val psrs_update_in_update_thm = store_thm(
    "psrs_update_in_update_thm",
    ``((0,CPSR) =+ psrs (0,CPSR) with IT := (psrs (0,CPSR)).IT) psrs = psrs ``,
    RW_TAC (srw_ss())  [boolTheory.FUN_EQ_THM]
      THEN EVAL_TAC
      THEN RW_TAC (srw_ss())  [ARMpsr_component_equality]);



val take_undef_instr_exception_constlem = store_thm(
    "take_undef_instr_exception_constlem",
    ``(access_violation s) ==> (take_undef_instr_exception <|proc:=0|> s = ValueState () s)``,
    EVAL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN `!(x:unit). x = ()` by (Cases_on `x` THEN EVAL_TAC)
       THEN SPEC_ASSUM_TAC (``!x. X``, [``ARB:unit``])
       THEN FULL_SIMP_TAC (srw_ss()) []);


val take_undef_instr_exception_av_thm = store_thm(
    "take_undef_instr_exception_av_thm",
     ``preserve_relation_mmu (take_undef_instr_exception <|proc:=0|>) (\s. (ARM_MODE s = 16w) /\ (access_violation s)) (assert_mode 16w) priv_mode_constraints priv_mode_similar``,
     MP_TAC reflex_priv_mode_constraints_thm
       THEN RW_TAC (srw_ss()) [preserve_relation_mmu_def, take_undef_instr_exception_constlem, assert_mode_def, untouched_refl, reflexive_comp_def]);


val take_undef_instr_exception_combine_thm = store_thm(
    "take_undef_instr_exception_combine_thm",
    ``(preserve_relation_mmu (take_undef_instr_exception <|proc:=0|>) (\s. (ARM_MODE s = 16w) /\ (~access_violation s)) (assert_mode 27w) priv_mode_constraints priv_mode_similar) ==> (preserve_relation_mmu (take_undef_instr_exception <|proc:=0|>) (assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints priv_mode_similar)``,
    MP_TAC take_undef_instr_exception_av_thm
    THEN RW_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, comb_mode_def]
    THEN IMP_RES_TAC similarity_implies_equal_av_thm
    THEN SPEC_ASSUM_TAC (``!g s s'. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
    THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []
    THEN Cases_on `access_violation s2` THEN FULL_SIMP_TAC (srw_ss()) []);










