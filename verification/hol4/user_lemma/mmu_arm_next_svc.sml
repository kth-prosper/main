;

(* Step 1: modes reachable with bad PC *)

val bad_PC_lem = store_thm(
    "bad_PC_lem",
    ``(mmu_requirements s g) ==>
      ((assert_mode 16w) s)  ==>
      (~aligned_word_readable s  ((s.psrs (0,CPSR)).T) (s.registers (0,RName_PC))) ==>
      (intrpt <> HW_Reset)   ==>
      (mmu_arm_next intrpt s = ValueState () t)
     ==> (little_mode_mix t)``,
     RW_TAC (srw_ss()) [mmu_arm_next_def, waiting_for_interrupt_def, readT_def, clear_wait_for_interrupt_def, writeT_def] THEN1 FULL_SIMP_TAC (srw_ss()) [little_mode_mix_def, assert_mode_def, empty_accesses_mode_lem]
     THENL [UNDISCH_ALL_TAC THEN CASE_TAC THEN RW_TAC (srw_ss()) []
               THEN ASSUME_TAC (SPECL [``a:(string # Encoding # word4 # ARMinstruction)``, ``b:arm_state``, ``(s with accesses := [])``, ``g:word32``] (GEN_ALL fetch_instr_av_lem))
               THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_aligned_word_readable_lem]
               THEN RES_TAC
               THEN UNDISCH_ALL_TAC THEN (REPEAT CASE_TAC) THEN RW_TAC(srw_ss()) []
               THEN ASSUME_TAC (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 fetch_instruction_thm)))
               THEN ASSUME_TAC take_prefetch_abort_exception_comb_thm
               THEN ASSUME_TAC reflex_priv_mode_similar_thm
               THEN IMP_RES_TAC downgrade_thm
               THEN FULL_SIMP_TAC (srw_ss()) [keep_mode_relation_def, keep_untouched_relation_def]
               THEN SPEC_ASSUM_TAC (``!g s s' x. X``, [``g:word32``, ``(s with accesses := [])``, ``b:arm_state``, ``(q,r):(string # Encoding # word4 # ARMinstruction)``])
               THEN SPEC_ASSUM_TAC (``!g s s'. X``, [``g:word32``, ``(b with accesses := [])``, ``t:arm_state``])
               THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_mode_lem, assert_mode_def, empty_accesses_untouched_lem]
               THEN RES_TAC
               THEN IMP_RES_TAC untouched_mmu_setup_lem
               THEN RES_TAC
               THEN FULL_SIMP_TAC (srw_ss()) [little_mode_mix_def, comb_mode_def, assert_mode_def],
            ASSUME_TAC take_fiq_exception_comb_thm,
            ASSUME_TAC take_irq_exception_comb_thm]
     THEN FULL_SIMP_TAC (srw_ss()) [seqT_def]
     THEN UNDISCH_ALL_TAC THEN CASE_TAC THEN RW_TAC(srw_ss()) []
     THEN Cases_on `a`
     THEN ASSUME_TAC reflex_priv_mode_similar_thm
     THEN IMP_RES_TAC downgrade_thm
     THEN FULL_SIMP_TAC (srw_ss()) [keep_mode_relation_def]
     THEN SPEC_ASSUM_TAC (``!g s s'. X``, [``g:word32``, ``(s with accesses := [])``, ``b:arm_state``])
     THEN FULL_SIMP_TAC (srw_ss()) [empty_accesses_requirements_lem, empty_accesses_mode_lem, assert_mode_def, empty_accesses_untouched_lem]
     THEN RES_TAC
     THEN FULL_SIMP_TAC (srw_ss()) [little_mode_mix_def, comb_mode_def, assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def]);



(* Step 2: the best contract we can offer *)


val mmu_arm_next_svc_thm = store_thm(
    "mmu_arm_next_svc_thm",
    ``(irpt <> HW_Reset) ==> preserve_relation_mmu (mmu_arm_next irpt) (assert_mode 16w) mode_mix priv_mode_constraints_v4 priv_mode_similar``,
    MP_TAC mmu_arm_next_thm
       THEN RW_TAC (srw_ss()) [preserve_relation_mmu_def]
       THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
       THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (srw_ss()) [priv_mode_constraints_v4_def, LET_DEF]
       THEN IMP_RES_TAC similarity_implies_equal_mode_thm
       THEN `(s1.psrs (0,CPSR)).T =  (s2.psrs (0,CPSR)).T` by FULL_SIMP_TAC (srw_ss()) [similar_def]
       THEN Cases_on `ARM_MODE s1' = 19w` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [ALL_TAC, METIS_TAC []]   
       THEN `(s1'.psrs (0,SPSR_svc)) =  (s1.psrs (0,CPSR))` by FULL_SIMP_TAC (srw_ss()) [priv_mode_constraints_v2_def]
       THEN `(s2'.psrs (0,SPSR_svc)) =  (s2.psrs (0,CPSR))` by FULL_SIMP_TAC (srw_ss()) [priv_mode_constraints_v2_def]
       THEN IMP_RES_TAC untouched_mmu_setup_lem
       THEN FULL_SIMP_TAC (srw_ss()) [priv_mode_constraints_v2_def]
       THEN Cases_on `a`
       THEN IMP_RES_TAC similarity_implies_equal_mode_thm
       THEN ASSUME_TAC (SPECL [``s1':arm_state``, ``s1:arm_state``, ``irpt:HWInterrupt``, ``g:word32``] (GEN_ALL bad_PC_lem))
       THEN ASSUME_TAC (SPECL [``s2':arm_state``, ``s2:arm_state``, ``irpt:HWInterrupt``, ``g:word32``] (GEN_ALL bad_PC_lem))  
       THEN ASSUME_TAC (SPECL [``s1':arm_state``, ``s1:arm_state``, ``(s1.psrs (0,CPSR)).T``, ``g:word32``, ``(s1.registers (0,RName_PC))``] (GEN_ALL global_aligned_word_readable_lem))
       THEN ASSUME_TAC (SPECL [``s2':arm_state``, ``s2:arm_state``, ``(s2.psrs (0,CPSR)).T``, ``g:word32``, ``(s2.registers (0,RName_PC))``] (GEN_ALL global_aligned_word_readable_lem))
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THENL [Cases_on `(s1.psrs (0,CPSR)).J` THEN FULL_SIMP_TAC (srw_ss()) [get_pc_value_def, LET_DEF, InstrSet2num_thm]
                 THEN CCONTR_TAC
                 THEN (`¬(aligned_word_readable s1 (s1.psrs (0,CPSR)).T  (s1.registers (0,RName_PC)))` by FULL_SIMP_TAC (srw_ss()) [])
                 THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [little_mode_mix_def],
              Cases_on `(s1.psrs (0,CPSR)).J` THEN FULL_SIMP_TAC (srw_ss()) [get_pc_value_def, LET_DEF, InstrSet2num_thm]
                 THEN CCONTR_TAC
                 THEN (`¬(aligned_word_readable s1 (s1.psrs (0,CPSR)).T  (s1.registers (0,RName_PC)))` by FULL_SIMP_TAC (srw_ss()) [])
                 THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [little_mode_mix_def],
              Cases_on `(s2.psrs (0,CPSR)).J` THEN FULL_SIMP_TAC (srw_ss()) [get_pc_value_def, LET_DEF, InstrSet2num_thm]
                 THEN CCONTR_TAC
                 THEN (`¬(aligned_word_readable s2 (s2.psrs (0,CPSR)).T (s2.registers (0,RName_PC)))` by FULL_SIMP_TAC (srw_ss()) [])
                 THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [little_mode_mix_def],
              Cases_on `(s2.psrs (0,CPSR)).J` THEN FULL_SIMP_TAC (srw_ss()) [get_pc_value_def, LET_DEF, InstrSet2num_thm]
                 THEN CCONTR_TAC
                 THEN (`¬(aligned_word_readable s2 (s2.psrs (0,CPSR)).T  (s2.registers (0,RName_PC)))` by FULL_SIMP_TAC (srw_ss()) [])
                 THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [little_mode_mix_def]]);



(* Step 3: relate v4 and v3 of pmc *)

val pmc_34_lem = store_thm(
    "pmc_34_lem",
    ``(mmu_requirements s1 g) ==> (priv_mode_constraints_v4 g s0 s1) ==> (priv_mode_constraints_v3 g s0 s1)``,
    RW_TAC (srw_ss()) [priv_mode_constraints_v3_def, priv_mode_constraints_v4_def] 
       THEN `guest1 <> guest2` by FULL_SIMP_TAC (srw_ss()) [guest1_def, guest2_def, global_vm_0_add_axiom, global_vm_1_add_axiom]
       THEN IMP_RES_TAC mmu_requirements_simp 
       THEN RES_TAC
       THEN FULL_SIMP_TAC (srw_ss()) [mmu_requirements_pure_def, aligned_word_readable_def]
       THEN PAT_ASSUM ``!add iw. X`` (fn th => ASSUME_TAC (SPECL [``s1.registers (0,RName_LRsvc) + 0xFFFFFFFEw``, ``F``] th)
                                          THEN ASSUME_TAC (SPECL [``s1.registers (0,RName_LRsvc) + 0xFFFFFFFCw``, ``F``] th))
       THEN UNDISCH_ALL_TAC 
       THEN RW_TAC (srw_ss()) [negated_inequalities_unsigned_lem]
       THEN FULL_SIMP_TAC (srw_ss()) [address_border, negated_inequalities_unsigned_lem, negated_and_or, address_trans]
       THEN METIS_TAC [address_border, negated_inequalities_unsigned_lem, negated_and_or, address_trans]);





(* Step 4: the contract finally used for the switching lemma *)

val mmu_arm_next_comb_thm = store_thm(
    "mmu_arm_next_comb_thm",
    ``(irpt <> HW_Reset) ==> preserve_relation_mmu (mmu_arm_next irpt) (assert_mode 16w) mode_mix priv_mode_constraints_v3 priv_mode_similar``,
    STRIP_TAC
      THEN IMP_RES_TAC mmu_arm_next_svc_thm
      THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [preserve_relation_mmu_def]
      THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
      THEN RES_TAC THEN FULL_SIMP_TAC (srw_ss()) []
      THEN IMP_RES_TAC untouched_mmu_setup_lem
      THEN IMP_RES_TAC pmc_34_lem
      THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []);


