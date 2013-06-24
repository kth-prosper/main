;


val no_armv4_axiom = new_axiom("no_armv4_axiom", ``!s. ((ARMinfo_arch o arm_state_information) s) <> ARMv4``);


val fetch_instruction_thm = prove_and_save_s (``fetch_instruction <|proc:=0|> 
                                       (\a. read_memA <|proc:=0|> (a, 4) >>= (\d. return (word32 d))) 
                                       (\a. read_memA <|proc:=0|> (a, 2) >>= (\d. return (word16 d)))``,
                                       "fetch_instruction_thm");


val instr_set_and_T_flag_thm = store_thm(
    "instr_set_and_T_flag_thm",
    ``!s.  (~access_violation s) ==> (((s.psrs(0,CPSR)).T) ==> ((actual_instr_set <|proc:=0|> s = ValueState InstrSet_Thumb s) \/ (actual_instr_set <|proc:=0|> s = ValueState InstrSet_ThumbEE s))) /\ ((~((s.psrs(0,CPSR)).T)) ==> ((actual_instr_set <|proc:=0|> s = ValueState InstrSet_ARM s) \/ (actual_instr_set <|proc:=0|> s = ValueState InstrSet_Jazelle s)))``,
    STRIP_TAC
      THEN MP_TAC (SPEC ``s:arm_state`` no_armv4_axiom)
      THEN EVAL_TAC
      THEN REPEAT STRIP_TAC
      THEN RW_TAC (srw_ss()) []
      THEN (REPEAT (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [] THEN EVAL_TAC)));

val align_248 =  numLib.REDUCE_RULE (Drule.LIST_CONJ (List.map (fn t => Q.SPEC t align_slice) [`1`,`2`,`3`]));



val align_lem = Q.prove(
  `(!b:word32. align(b,2) + (0 -- 0) b = b) /\
   (!b:word32. align(b,4) + (1 -- 0) b = b) /\
   (!b:word32. align(b,8) + (2 -- 0) b = b)`,
  SRW_TAC [wordsLib.WORD_EXTRACT_ss] [align_248]);



val read_memA4_av_lem = store_thm(
    "read_memA4_av_lem",
    ``!pc. (mmu_requirements s g) ==>
       ((read_memA <|proc:=0|> (pc, 4)) s = ValueState x t) ==> 
       (    ¬permitted_byte_pure (pc) F s.coprocessors.state.cp15.C1
                                        s.coprocessors.state.cp15.C2
                                        s.coprocessors.state.cp15.C3 F s.memory
        \/  ¬permitted_byte_pure (align(pc,4)) F s.coprocessors.state.cp15.C1
                                                 s.coprocessors.state.cp15.C2 
						 s.coprocessors.state.cp15.C3 F s.memory
        \/ ¬permitted_byte_pure (align (pc,4) + 1w) F s.coprocessors.state.cp15.C1
	                                              s.coprocessors.state.cp15.C2 
						      s.coprocessors.state.cp15.C3 F s.memory
        \/ ¬permitted_byte_pure (align (pc,4) + 2w) F s.coprocessors.state.cp15.C1
	                                              s.coprocessors.state.cp15.C2 
						      s.coprocessors.state.cp15.C3 F s.memory
        \/ ¬permitted_byte_pure (align (pc,4) + 3w) F s.coprocessors.state.cp15.C1
	                                              s.coprocessors.state.cp15.C2 
						      s.coprocessors.state.cp15.C3 F s.memory)
       ==> (access_violation t)``,
    RW_TAC (srw_ss()) []
       THENL (map (fn byte => (`!other. access_violation (s with accesses updated_by CONS (MEM_READ (^byte)) o other)` by (METIS_TAC [malicious_read2, access_violation_req, mmu_requirement_accesses_update_lem2]))) [``pc:word32``, ``(align(pc,4)):word32``, ``(align(pc,4) + 1w):word32``, ``(align(pc,4) +2w):word32``, ``(align(pc,4) +3w):word32``])
       THEN UNDISCH_TAC `` read_memA <|proc := 0|> (pc,4) s = ValueState x t``
       THEN EVAL_TAC
       THEN (REPEAT (CHANGED_TAC ((TRY (UNDISCH_MATCH_TAC ``X = ValueState x t``)) THEN RW_TAC (srw_ss()) [])))
       THENL (List.tabulate(14, (fn n => if ((n = 2) orelse (n =3)) 
                         then MP_TAC (blastLib.BBLAST_PROVE ``(((1 -- 0) (pc:word32)) = 0w) \/ (((1 -- 0) (pc:word32)) = 1w) \/ (((1 -- 0) (pc:word32)) = 2w) \/ (((1 -- 0) (pc:word32)) = 3w)``)
                                THEN RW_TAC (srw_ss()) []
                                THEN CCONTR_TAC 
                                THEN FULL_SIMP_TAC (srw_ss()) []
                                THEN ASSUME_TAC (SPEC ``pc:word32`` (CONJUNCT1 (CONJUNCT2 align_lem)))
                                THEN UNDISCH_ALL_TAC 
                                THEN RW_TAC (srw_ss()) [] 
                                THEN CCONTR_TAC 
                                THEN FULL_SIMP_TAC (srw_ss()) []
                                THEN UNDISCH_ALL_TAC 
                                THEN RW_TAC (srw_ss()) []
                                THEN FULL_SIMP_TAC (srw_ss()) [aligned_def, align_def]
                         else FULL_SIMP_TAC (srw_ss()) [aligned_def]
                                THEN METIS_TAC [malicious_read, access_violation_req, mmu_requirement_accesses_update_lem]))));


val read_memA2_av_lem = store_thm(
    "read_memA2_av_lem",
    ``!pc. (mmu_requirements s g) ==>
       ((read_memA <|proc:=0|> (pc, 2)) s = ValueState x t) ==> 
       (    ¬permitted_byte_pure (pc) F s.coprocessors.state.cp15.C1
                                        s.coprocessors.state.cp15.C2
                                        s.coprocessors.state.cp15.C3 F s.memory
        \/  ¬permitted_byte_pure (align(pc,2)) F s.coprocessors.state.cp15.C1
                                                 s.coprocessors.state.cp15.C2 
						 s.coprocessors.state.cp15.C3 F s.memory
        \/ ¬permitted_byte_pure (align (pc,2) + 1w) F s.coprocessors.state.cp15.C1
	                                              s.coprocessors.state.cp15.C2 
						      s.coprocessors.state.cp15.C3 F s.memory)
       ==> (access_violation t)``,
    RW_TAC (srw_ss()) []
       THENL (map (fn byte => (`!other. access_violation (s with accesses updated_by CONS (MEM_READ (^byte)) o other)` by (METIS_TAC [malicious_read2, access_violation_req, mmu_requirement_accesses_update_lem2]))) [``pc:word32``, ``(align(pc,2)):word32``, ``(align(pc,2) + 1w):word32``])
       THEN UNDISCH_TAC `` read_memA <|proc := 0|> (pc,2) s = ValueState x t``
       THEN EVAL_TAC
       THEN (REPEAT (CHANGED_TAC ((TRY (UNDISCH_MATCH_TAC ``X = ValueState x t``)) THEN RW_TAC (srw_ss()) [])))
       THENL (List.tabulate(10, (fn n => if ((n = 2) orelse (n =3)) 
                         then MP_TAC (blastLib.BBLAST_PROVE ``(((0 -- 0) (pc:word32)) = 0w) \/ (((0 -- 0) (pc:word32)) = 1w)``)
                                THEN RW_TAC (srw_ss()) []
                                THEN CCONTR_TAC 
                                THEN FULL_SIMP_TAC (srw_ss()) []
                                THEN ASSUME_TAC (SPEC ``pc:word32`` (CONJUNCT1 (align_lem)))
                                THEN UNDISCH_ALL_TAC 
                                THEN RW_TAC (srw_ss()) [] 
                                THEN CCONTR_TAC 
                                THEN FULL_SIMP_TAC (srw_ss()) []
                                THEN UNDISCH_ALL_TAC 
                                THEN RW_TAC (srw_ss()) []
                                THEN FULL_SIMP_TAC (srw_ss()) [aligned_def, align_def]
                         else FULL_SIMP_TAC (srw_ss()) [aligned_def]
                                THEN METIS_TAC [malicious_read, access_violation_req, mmu_requirement_accesses_update_lem]))));


val fetch_arm_av_lem = store_thm(
    "fetch_arm_av_lem",
    `` (mmu_requirements s g) ==>
       (    ¬permitted_byte_pure (s.registers (0,RName_PC)) F s.coprocessors.state.cp15.C1
                                        s.coprocessors.state.cp15.C2
                                        s.coprocessors.state.cp15.C3 F s.memory
        \/  ¬permitted_byte_pure (align(s.registers (0,RName_PC),4)) F s.coprocessors.state.cp15.C1
                                                 s.coprocessors.state.cp15.C2 
						 s.coprocessors.state.cp15.C3 F s.memory
        \/ ¬permitted_byte_pure (align (s.registers (0,RName_PC),4) + 1w) F s.coprocessors.state.cp15.C1
	                                              s.coprocessors.state.cp15.C2 
						      s.coprocessors.state.cp15.C3 F s.memory
        \/ ¬permitted_byte_pure (align (s.registers (0,RName_PC),4) + 2w) F s.coprocessors.state.cp15.C1
	                                              s.coprocessors.state.cp15.C2 
						      s.coprocessors.state.cp15.C3 F s.memory
        \/ ¬permitted_byte_pure (align (s.registers (0,RName_PC),4) + 3w) F s.coprocessors.state.cp15.C1
	                                              s.coprocessors.state.cp15.C2 
						      s.coprocessors.state.cp15.C3 F s.memory) ==>
       (((fetch_arm <|proc:=0|> (\a. read_memA <|proc:=0|> (a, 4) >>= (\d. return (word32 d)))) s) = ValueState x t) 
       ==> (access_violation t)``,
    NTAC 2 DISCH_TAC
      THEN PROTECTED_OR_RW_TAC [armTheory.fetch_arm_def, read_pc_def, readT_def, seqT_def, parT_def, arch_version_def, read__reg_def, read_arch_def, constT_def] THEN PROTECTED_OR_RW_TAC []
      THEN Cases_on `read_memA <|proc := 0|> (s.registers (0,RName_PC),4) s` THEN PROTECTED_OR_SIMP_TAC []
      THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [read_memA4_av_lem] THEN METIS_TAC [read_memA4_av_lem] );


val fetch_thumb_av_lem = store_thm(
    "fetch_thumb_av_lem",
    `` (mmu_requirements s g) ==>
       (    ¬permitted_byte_pure (s.registers (0,RName_PC)) F s.coprocessors.state.cp15.C1
                                        s.coprocessors.state.cp15.C2
                                        s.coprocessors.state.cp15.C3 F s.memory
        \/  ¬permitted_byte_pure (align(s.registers (0,RName_PC),2)) F s.coprocessors.state.cp15.C1
                                                 s.coprocessors.state.cp15.C2 
						 s.coprocessors.state.cp15.C3 F s.memory
        \/ ¬permitted_byte_pure (align (s.registers (0,RName_PC),2) + 1w) F s.coprocessors.state.cp15.C1
	                                              s.coprocessors.state.cp15.C2 
						      s.coprocessors.state.cp15.C3 F s.memory) ==>
       (((fetch_thumb <|proc:=0|> bEE (\a. read_memA <|proc:=0|> (a, 2) >>= (\d. return (word16 d)))) s) = ValueState x t) 
       ==> (access_violation t)``,
      NTAC 2 DISCH_TAC
         THEN PROTECTED_OR_RW_TAC [armTheory.fetch_thumb_def, read_pc_def, readT_def, seqT_def, parT_def, arch_version_def, read__reg_def, read_arch_def, constT_def, read_cpsr_def, read__psr_def] THEN PROTECTED_OR_RW_TAC []
         THEN Cases_on `read_memA <|proc := 0|> (s.registers (0,RName_PC),2) s` THEN PROTECTED_OR_SIMP_TAC []
         THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [read_memA2_av_lem] THEN  METIS_TAC [read_memA2_av_lem]);




val fetch_instr_av_lem = store_thm(
    "fetch_instr_av_lem",
    ``(mmu_requirements s g) ==>
      (~aligned_word_readable s ((s.psrs (0,CPSR)).T) (s.registers (0,RName_PC))) ==>
      ((fetch_instruction <|proc:=0|> (\a. read_memA <|proc:=0|> (a, 4) >>= (\d. return (word32 d))) 
                                       (\a. read_memA <|proc:=0|> (a, 2) >>= (\d. return (word16 d))) s) = ValueState x t) 
      ==> (access_violation t)``,
    Q.ABBREV_TAC `readword = (\a. read_memA <|proc:=0|> (a, 4) >>= (\d. return (word32 d)))`
       THEN Q.ABBREV_TAC `readhalfword = (\a. read_memA <|proc:=0|> (a, 2) >>= (\d. return (word16 d)))`
       THEN RW_TAC (srw_ss()) [armTheory.fetch_instruction_def, seqT_def, aligned_word_readable_def]
       THENL [(Cases_on `(s.psrs (0,CPSR)).T`), ALL_TAC, ALL_TAC, ALL_TAC, ALL_TAC, ALL_TAC, ALL_TAC]
       THEN (Cases_on `access_violation s` 
              THENL [FULL_SIMP_TAC (srw_ss()) [armTheory.actual_instr_set_def, read_arch_def, seqT_def, readT_def] 
                       THEN METIS_TAC [],
                    IMP_RES_TAC instr_set_and_T_flag_thm THEN FULL_SIMP_TAC (srw_ss()) [errorT_def] 
                       THEN FIRST [Q.UNABBREV_TAC `readhalfword` 
                                      THEN IMP_RES_TAC fetch_thumb_av_lem 
                                      THEN NO_TAC,
                                   Q.UNABBREV_TAC `readword` 
                                      THEN IMP_RES_TAC fetch_arm_av_lem]]));





