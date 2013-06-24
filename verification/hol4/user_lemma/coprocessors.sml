;
val coproc_accepted_ax =  new_axiom("coproc_accepted_ax", 
                          ``!s s' inst accept. (assert_mode 16w s) ==> (coproc_accepted <|proc:=0|> inst s = ValueState accept s') ==> (~accept)``);


val coproc_accepted_constlem = store_thm(
    "coproc_accepted_constlem",
    ``!s inst. ?x. coproc_accepted <|proc:=0|> inst s = ValueState x s``,
    REPEAT STRIP_TAC THEN EVAL_TAC THEN RW_TAC (srw_ss()) [])


val coproc_accepted_usr_def = store_thm(
    "coproc_accepted_usr_def",
    ``!s inst. (assert_mode 16w s) ==> (coproc_accepted <|proc:=0|> inst s = ValueState F s)``,
    RW_TAC (srw_ss()) []
       THEN Cases_on `coproc_accepted <|proc := 0|> inst s` 
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN IMP_RES_TAC coproc_accepted_ax
       THEN ASSUME_TAC (SPECL [``s:arm_state``, ``inst:CPinstruction``] coproc_accepted_constlem)
       THEN (NTAC 2 (FULL_SIMP_TAC (srw_ss()) [])));


val coproc_accepted_empty_thm = store_thm(
    "coproc_accepted_empty_thm",
    ``!inst. preserve_relation_mmu (coproc_accepted <|proc:=0|> inst) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim``,
    RW_TAC (srw_ss()) [coproc_accepted_usr_def, preserve_relation_mmu_def, untouched_def, empty_unt_def, empty_sim_def] THEN RW_TAC (srw_ss()) []);

val coproc_accepted_thm = save_thm("coproc_accepted_thm", (MATCH_MP extras_lem2 (SPEC_ALL coproc_accepted_empty_thm)));


val coproc_accepted_simp_lem = store_thm(
    "coproc_accepted_simp_lem",
    ``!s inst ifcomp elsecomp.
        (assert_mode 16w s) ==>
        ((coproc_accepted <|proc:=0|> inst >>=
                (λaccepted.
                   if ¬accepted then
                     ifcomp
                   else
                     elsecomp)) s
         =        
         (coproc_accepted <|proc:=0|> inst >>=
                (λaccepted.ifcomp)) s)``,
     REPEAT STRIP_TAC
        THEN FULL_SIMP_TAC (srw_ss()) [seqT_def]
        THEN Cases_on `coproc_accepted <|proc := 0|> inst s` 
        THEN IMP_RES_TAC coproc_accepted_ax
        THEN FULL_SIMP_TAC (srw_ss()) []);


val coproc_accepted_simp_rel_lem = store_thm(
    "coproc_accepted_simp_rel_lem",
    ``!coproc ThisInstr ifcomp elsecomp inv2 uf uy.
      (preserve_relation_mmu
        (coproc_accepted <|proc:=0|> (coproc,ThisInstr) >>=
                (λaccepted.
                   if ¬accepted then
                     ifcomp
                   else
                     elsecomp)) (assert_mode 16w) (inv2) uf uy)
        = 
      (preserve_relation_mmu
        (coproc_accepted <|proc:=0|> (coproc,ThisInstr) >>=
                (λaccepted. ifcomp)) (assert_mode 16w) (inv2) uf uy)``,
     RW_TAC (srw_ss()) [coproc_accepted_simp_lem, preserve_relation_mmu_def]);



val coproc_accepted_simp_preserves_help_comb_thm = prove_and_save_p_helper (``coproc_accepted <|proc := 0|> (coproc,ThisInstr) >>=
            (\accepted. take_undef_instr_exception <|proc:=0|>)``, "coproc_accepted_simp_preserves_comb_help_thm");



val coproc_accepted_simp_preserves_comb_thm = store_thm(
    "coproc_accepted_simp_preserves_comb_thm",
    ``!coproc ThisInstr elsecomp.
      preserve_relation_mmu
        (coproc_accepted <|proc:=0|> (coproc,ThisInstr) >>=
                (λaccepted.
                   if ¬accepted then
                     take_undef_instr_exception <|proc:=0|>
                   else
                     elsecomp)) (assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints
     priv_mode_similar``,
     RW_TAC (srw_ss()) [coproc_accepted_simp_rel_lem, coproc_accepted_simp_preserves_help_comb_thm]);


add_to_simplist coproc_accepted_simp_preserves_comb_thm;



