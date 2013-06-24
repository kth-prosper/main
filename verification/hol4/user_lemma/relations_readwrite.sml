val equal_mem_lem = store_thm(
    "equal_mem_lem",
    `` !s1 s2 g (add:bool[32]) is_write.
       (similar g s1 s2)       ==>
       (mmu_requirements s1 g) ==>
       (mmu_requirements s2 g) 
    ==>
       ((s1.memory add) = (s2.memory add))
     \/
       (
        ~ permitted_byte_pure add is_write s1.coprocessors.state.cp15.C1
                                           s1.coprocessors.state.cp15.C2
                                           s1.coprocessors.state.cp15.C3
                                           F s1.memory
        /\
        ~ permitted_byte_pure add is_write s2.coprocessors.state.cp15.C1
                                           s2.coprocessors.state.cp15.C2
                                           s2.coprocessors.state.cp15.C3
                                           F s2.memory
       )``,
   REPEAT STRIP_TAC
       THEN `mmu_requirements_pure s1 g` by FULL_SIMP_TAC (srw_ss()) [mmu_requirements_simp]
       THEN `mmu_requirements_pure s2 g` by FULL_SIMP_TAC (srw_ss()) [mmu_requirements_simp]
       THEN MP_TAC (SPEC ``add:bool[32]`` negated_and_or)
       THEN MP_TAC (SPEC ``add:word32`` address_border)
       THEN FULL_SIMP_TAC (srw_ss()) [mmu_requirements_pure_def, similar_def]
       THEN METIS_TAC []);



val stay_similar_lem = store_thm(
    "stay_similar_lem",
    ``!s1 s2 g add x. 
      (mmu_requirements s1 g) ==>
      (mmu_requirements s2 g) ==> 
      (similar g s1 s2) 
     ==> ((similar g (s1 with accesses updated_by CONS (MEM_READ add)) (s2 with accesses updated_by CONS (MEM_READ add)))
     /\  (similar g (s1 with accesses updated_by CONS (MEM_WRITE add x)) (s2 with accesses updated_by CONS (MEM_WRITE add x))))``,
     NTAC 8 STRIP_TAC
        THEN FULL_SIMP_TAC (srw_ss()) [similar_def, user_regs_from_state_def, LET_DEF, user_regs_from_list_def, read__reg_def, readT_def]
        THEN MP_TAC (SPECL [``add:word32``, ``x:word8``]  mmu_requirement_accesses_update_lem)
        THEN STRIP_TAC
        THEN RES_TAC
        THEN MP_TAC access_violation_req
        THEN STRIP_TAC
        THEN RES_TAC
        THEN FULL_SIMP_TAC (srw_ss()) [access_violation_pure_def]
        THEN PURE_ONCE_REWRITE_TAC [check_accesses_pure_def]
        THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
        THEN `mmu_requirements_pure s1 g` by FULL_SIMP_TAC (srw_ss()) [mmu_requirements_simp]
        THEN `mmu_requirements_pure s2 g` by FULL_SIMP_TAC (srw_ss()) [mmu_requirements_simp]
        THEN MP_TAC same_setup_same_rights_lem 
        THEN STRIP_TAC 
        THEN RES_TAC
        THEN FULL_SIMP_TAC (srw_ss()) [equal_user_register_def]
        THEN METIS_TAC []);

val keep_mode_on_accesses_update_lem = store_thm(
    "keep_mode_on_accesses_update_lem",
    ``!m s add x. 
      (ARM_MODE s = m) 
     ==> 
        (ARM_MODE (s with accesses updated_by CONS (MEM_READ add)) = m) /\
        (ARM_MODE (s with accesses updated_by CONS (MEM_WRITE add x)) = m)``,
     NTAC 4  STRIP_TAC THEN EVAL_TAC);



val read_mem1_mode_thm = store_thm(
    "read_mem1_mode_thm",
    ``!add. keep_mode_relation (read_mem1 <|proc:=0|> add) (assert_mode 16w) (assert_mode 16w)``,
    RW_TAC (srw_ss()) [keep_mode_relation_def, writeT_def, readT_def,  seqT_def, read_mem1_def, assert_mode_def]
       THEN UNDISCH_ALL_TAC
       THEN IF_CASES_TAC
       THEN STRIP_TAC
       THEN REPEAT (EVAL_TAC THEN RW_TAC (srw_ss()) []));



val read_mem1_similar_thm = store_thm (
    "read_mem1_similar_thm",
    ``!add. keep_similar_relation (read_mem1 <|proc:=0|> add) (assert_mode 16w) empty_sim``,
    PURE_ONCE_REWRITE_TAC [keep_similar_relation_def] 
       THEN NTAC 8 STRIP_TAC
       THEN Cases_on `read_mem1 <|proc:=0|> add s1`
       THEN Cases_on `read_mem1 <|proc:=0|> add s2`
       THEN FULL_SIMP_TAC (srw_ss()) [empty_sim_def]
       THENL [FULL_SIMP_TAC (srw_ss()) [read_mem1_def, writeT_def, readT_def,  seqT_def]
                 THEN (`b = (s1 with accesses updated_by CONS (MEM_READ add))` by 
                            (Cases_on `access_violation (s1 with accesses updated_by CONS (MEM_READ add))`
                               THEN FULL_SIMP_TAC (srw_ss()) []))
                 THEN (`b' = (s2 with accesses updated_by CONS (MEM_READ add))` by 
                            (Cases_on `access_violation (s2 with accesses updated_by CONS (MEM_READ add))`
                               THEN FULL_SIMP_TAC (srw_ss()) []))
                 THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``s2:arm_state``, ``g:word32``, ``add:word32``, ``F``] equal_mem_lem)
                 THEN RES_TAC
                 THENL [`similar g b b'  = similar g s1 s2` by METIS_TAC [stay_similar_lem]
                           THEN Cases_on `access_violation (s2 with accesses updated_by CONS (MEM_READ add))` 
                           THEN Cases_on `access_violation (s1 with accesses updated_by CONS (MEM_READ add))` 
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN RES_TAC 
                           THEN FULL_SIMP_TAC (srw_ss()) [similar_def,arm_stepTheory.ARM_MODE_def, arm_stepTheory.ARM_READ_CPSR_def]
                           THEN METIS_TAC [],
                        ASSUME_TAC (SPECL [``add:word32``, ``x:word8``, ``s1:arm_state``, ``g:word32``] mmu_requirement_accesses_update_lem)
                           THEN ASSUME_TAC (SPECL [``add:word32``, ``x:word8``, ``s2:arm_state``, ``g:word32``] mmu_requirement_accesses_update_lem)
                           THEN ASSUME_TAC access_violation_req
                           THEN RES_TAC
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN MP_TAC  malicious_read
                           THEN STRIP_TAC
                           THEN RES_TAC
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN METIS_TAC [stay_similar_lem, keep_mode_on_accesses_update_lem]],
              FULL_SIMP_TAC (srw_ss()) [read_mem1_def, similar_def, seqT_def, writeT_def, readT_def]
                 THEN Cases_on `access_violation (s2 with accesses updated_by CONS (MEM_READ add))` 
                 THEN FULL_SIMP_TAC (srw_ss()) [],
              FULL_SIMP_TAC (srw_ss()) [read_mem1_def, similar_def, seqT_def, writeT_def, readT_def]
                 THEN Cases_on `access_violation (s1 with accesses updated_by CONS (MEM_READ add))` 
                 THEN FULL_SIMP_TAC (srw_ss()) [],
              FULL_SIMP_TAC (srw_ss()) [read_mem1_def, similar_def, seqT_def, writeT_def, readT_def]
                 THEN Cases_on `access_violation (s1 with accesses updated_by CONS (MEM_READ add))` 
                 THEN FULL_SIMP_TAC (srw_ss()) []]);


val read_mem1_ut_thm = store_thm (
    "read_mem1_ut_thm",
    ``!add. keep_untouched_relation (read_mem1 <|proc:=0|> add) (assert_mode 16w) strict_unt``,
    RW_TAC (srw_ss()) [keep_untouched_relation_def, read_mem1_def, seqT_def, writeT_def, readT_def, strict_unt_def]
       THEN Cases_on `access_violation (s with accesses updated_by CONS (MEM_READ add))`
       THEN FULL_SIMP_TAC (srw_ss()) [untouched_def, LET_DEF, assert_mode_def]
       THEN RW_TAC (srw_ss()) [keep_mode_on_accesses_update_lem]);


val read_mem1_strict_thm = store_thm(
    "read_mem1_strict_thm",
    ``!add. preserve_relation_mmu (read_mem1 <|proc:=0|> add) (assert_mode 16w) (assert_mode 16w) strict_unt empty_sim``,
    METIS_TAC [read_mem1_ut_thm, read_mem1_similar_thm, read_mem1_mode_thm, three_parts_thm]);

val read_mem1_thm = save_thm("read_mem1_thm", MATCH_MP extras_lem4 (SPEC_ALL read_mem1_strict_thm));

 

(* ======= write_mem1 ======== *)




val write_mem1_mode_thm = store_thm(
    "write_mem1_mode_thm",
    ``!add data. keep_mode_relation (write_mem1 <|proc:=0|> add data) (assert_mode 16w) (assert_mode 16w)``,
    RW_TAC (srw_ss()) [keep_mode_relation_def, writeT_def, readT_def,  seqT_def, write_mem1_def, assert_mode_def]
       THEN UNDISCH_ALL_TAC
       THEN IF_CASES_TAC
       THEN STRIP_TAC
       THEN REPEAT (EVAL_TAC THEN RW_TAC (srw_ss()) []));



val write_mem1_ut_thm = store_thm (
    "write_mem1_ut_thm",
    ``!add data. keep_untouched_relation (write_mem1 <|proc:=0|> add data) (assert_mode 16w) empty_unt``,
    RW_TAC (srw_ss()) [keep_untouched_relation_def, empty_unt_def]
       THEN FULL_SIMP_TAC (srw_ss()) [write_mem1_def, seqT_def, writeT_def, readT_def]
       THEN IMP_RES_TAC mmu_requirements_simp
       THEN FULL_SIMP_TAC (srw_ss()) [mmu_requirements_pure_def]
       THEN PAT_ASSUM ``!(add:word32) (is_write:bool). X`` (fn th => ASSUME_TAC (SPECL [``add:word32``, ``T:bool``] th))
       THEN ASSUME_TAC (SPEC ``add:word32`` address_complete)
       THEN Cases_on `g=guest1`
       THEN Cases_on `g=guest2`
       THEN (`guest1 <> guest2` by EVAL_TAC THEN FULL_SIMP_TAC (srw_ss()) [global_vm_0_add_axiom, global_vm_1_add_axiom] )
       THEN FULL_SIMP_TAC (srw_ss()) [] 
       THEN FIRST_PROVE
            [ASSUME_TAC (SPECL [``s:arm_state``, ``s with accesses updated_by CONS (MEM_WRITE add data)``] trivially_untouched_mmu_setup_lem)
                THEN FULL_SIMP_TAC (srw_ss()) []
                THEN ASSUME_TAC access_violation_req
                THEN RES_TAC
                THEN FULL_SIMP_TAC (srw_ss()) []
                THEN ASSUME_TAC  (SPECL [``s:arm_state``, ``s with accesses updated_by CONS (MEM_WRITE add data)``, ``add:word32``, ``data:word8``] malicious_write)
                THEN FULL_SIMP_TAC (srw_ss()) [untouched_def, LET_DEF]
                THEN RW_TAC (srw_ss()) [],
             UNDISCH_ALL_TAC
                THEN CASE_TAC
                THEN RW_TAC (srw_ss()) [untouched_def, LET_DEF]
                THEN (RW_TAC (srw_ss()) []
                      THEN EVAL_TAC 
                      THEN RW_TAC (srw_ss()) [inequal_by_inequalities])]);



val write_mem1_similar_thm = store_thm (
    "write_mem1_similar_thm",
    ``!add data. keep_similar_relation (write_mem1 <|proc:=0|> add data) (assert_mode 16w) empty_sim``,
    REPEAT STRIP_TAC
       THEN ASSUME_TAC (SPECL [``add:word32``, ``data:word8``] write_mem1_ut_thm)
       THEN FULL_SIMP_TAC (srw_ss()) [keep_similar_relation_def, assert_mode_def, keep_untouched_relation_def, empty_sim_def]
       THEN REPEAT STRIP_TAC
       THEN RES_TAC
       THEN FULL_SIMP_TAC (srw_ss())  [write_mem1_def, seqT_def, readT_def]
       THEN (REPEAT CASE_TAC) THEN FULL_SIMP_TAC (srw_ss()) [writeT_def] THEN IMP_RES_TAC stay_similar_lem
       THEN PAT_ASSUM ``!(x:word8) (add:word32). X`` (fn th => (ASSUME_TAC (SPECL [``data:word8``, ``add:word32``] th)))
       THEN RW_TAC (srw_ss()) []
       THEN THROW_AWAY_TAC ``similar g a b ==> X``
       THEN FULL_SIMP_TAC (srw_ss()) [similar_def, equal_user_register_def]
       THEN (REPEAT STRIP_TAC)
       THEN RES_TAC
       THEN UNDISCH_MATCH_TAC ``!(add:word32). X``
       THEN EVAL_TAC
       THEN (PROTECTED_RW_TAC ``(g:word32) = X`` ORELSE RW_TAC (srw_ss()) [])
       THEN IMP_RES_TAC untouched_mmu_setup_lem
       THEN IMP_RES_TAC mmu_requirement_accesses_update_lem
       THEN REPEAT (PAT_ASSUM ``!(x:word8) (add:word32). X`` (fn th => (ASSUME_TAC (SPECL [``data:word8``, ``add:word32``] th))))
       THEN ASSUME_TAC (SPECL [``(s1:arm_state) with accesses updated_by CONS (MEM_WRITE (add:word32) (data:word8))``,
                   ``s1 with  <|memory updated_by (add =+ data); accesses updated_by CONS (MEM_WRITE add data)|>``,
                   ``g:word32``] same_setup_same_av_lem)
       THEN ASSUME_TAC (SPECL [``(s2:arm_state) with accesses updated_by CONS (MEM_WRITE (add:word32) (data:word8))``,
                   ``s2 with  <|memory updated_by (add =+ data); accesses updated_by CONS (MEM_WRITE add data)|>``,
                   ``g:word32``] same_setup_same_av_lem)
       THEN FULL_SIMP_TAC (srw_ss()) [ARM_MODE_def, ARM_READ_CPSR_def]);


val write_mem1_empty_thm = store_thm(
    "write_mem1_empty_thm",
    ``!add data. preserve_relation_mmu (write_mem1 <|proc:=0|> add data) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim``,
    METIS_TAC [write_mem1_ut_thm, write_mem1_similar_thm, write_mem1_mode_thm, three_parts_thm]);

val write_mem1_thm = store_thm(
    "write_mem1_thm",
    ``!add data. preserve_relation_mmu (write_mem1 <|proc:=0|> add data) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar``,
    METIS_TAC [write_mem1_empty_thm, empty_extras_lem]);




(* read_mem *)


val read_mem_strict_thm = store_thm(
    "read_mem_pmc_thm",
    ``!desc size. preserve_relation_mmu (read_mem <|proc:=0|> (desc,size)) (assert_mode 16w) (assert_mode 16w) strict_unt empty_sim``,
    RW_TAC (srw_ss()) [read_mem_def, errorT_def, LET_DEF]
       THENL [RW_TAC (srw_ss()) [preserve_relation_mmu_def],
                 `!a. preserve_relation_mmu ((λi. read_mem1 <|proc:=0|> ((desc.paddress) + (n2w i))) a) (assert_mode 16w) (assert_mode 16w) strict_unt empty_sim` by METIS_TAC [read_mem1_thm]
                 THEN ASSUME_TAC reflex_empty_sim_thm
                 THEN ASSUME_TAC (SPEC ``16w:word5`` reflex_strict_unt_thm)
                 THEN ASSUME_TAC trans_strict_unt_thm
                 THEN IMP_RES_TAC forT_preserves_user_relation_thm
                 THEN FULL_SIMP_TAC (srw_ss()) []]);


val read_mem_pmc_thm = store_thm(
    "read_mem_pmc_thm",
    ``!desc size. preserve_relation_mmu (read_mem <|proc:=0|> (desc,size)) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar``,
    RW_TAC (srw_ss()) [read_mem_def, errorT_def, LET_DEF]
       THENL [RW_TAC (srw_ss()) [preserve_relation_mmu_def],
                 `!a. preserve_relation_mmu ((λi. read_mem1 <|proc:=0|> ((desc.paddress) + (n2w i))) a) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar` by METIS_TAC [read_mem1_thm]
                 THEN ASSUME_TAC reflex_priv_mode_similar_thm
                 THEN ASSUME_TAC reflex_priv_mode_constraints_thm
                 THEN ASSUME_TAC trans_priv_mode_constraints_thm
                 THEN IMP_RES_TAC forT_preserves_user_relation_thm
                 THEN FULL_SIMP_TAC (srw_ss()) []]);

(*
val read_mem_thm = save_thm("read_mem_thm", (MATCH_MP extras_lem2 (EQ_MP (SPEC ``(read_mem <|proc := 0|> (desc,size)):(word8 list M)`` (INST_TYPE [alpha |-> Type `:word8 list`] empty_extras_lem)) (SPEC_ALL read_mem_pmc_thm))));*)


val read_mem_thm = save_thm("read_mem_thm", MATCH_MP extras_lem4 (SPEC_ALL read_mem_strict_thm));


(* write_mem *)


val write_mem_pmc_thm = store_thm(
    "write_mem_pmc_thm",
    ``!desc size value. preserve_relation_mmu(write_mem <|proc:=0|> (desc,size) value) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar``,
    RW_TAC (srw_ss()) [write_mem_def, errorT_def, LET_DEF]
       THENL [RW_TAC (srw_ss()) [preserve_relation_mmu_def],
              RW_TAC (srw_ss()) [preserve_relation_mmu_def],
              ASSUME_TAC reflex_priv_mode_similar_thm
                 THEN ASSUME_TAC reflex_priv_mode_constraints_thm
                 THEN ASSUME_TAC trans_priv_mode_constraints_thm
                 THEN IMP_RES_TAC (SPECL [``(assert_mode 16w):arm_state->bool``, ``priv_mode_constraints``, ``priv_mode_similar``] constT_unit_preserving_lem)
                 THEN PAT_ASSUM ``preserve_relation_mmu X1 X2 X3 X4 X5`` (fn th => ASSUME_TAC (GEN ``u:(unit list)`` th))
                 THEN `(preserve_relation_mmu_abs ((\u:(unit list). return ())) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar)` by FULL_SIMP_TAC (srw_ss()) [second_abs_lemma]
                 THEN  `!x. preserve_relation_mmu ((λi. write_mem1 <|proc:=0|> ((desc.paddress) + (n2w i)) (EL i value)) x) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar` by METIS_TAC [write_mem1_thm]
                 THEN IMP_RES_TAC forT_preserves_user_relation_thm
                 THEN (REPEAT (PAT_ASSUM ``!l h. X`` (fn th => ASSUME_TAC (SPECL [``0``, ``LENGTH (value:word8 list) - 1``] th))))
                 THEN (REPEAT (PAT_ASSUM ``!x. X`` (fn th => IMP_RES_TAC th)))
                 THEN (REPEAT (PAT_ASSUM ``~X`` (fn th => IMP_RES_TAC th)))        
                 THEN IMP_RES_TAC seqT_preserves_relation_uu_thm]);


val write_mem_thm = save_thm("write_mem_thm", (MATCH_MP extras_lem2 (EQ_MP (SPEC ``(write_mem <|proc := 0|> (desc,size) value):(unit M)`` (INST_TYPE [alpha |-> Type `:unit`] empty_extras_lem)) (SPEC_ALL write_mem_pmc_thm))));


