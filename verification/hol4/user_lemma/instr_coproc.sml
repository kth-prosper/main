;

g `preserve_relation_mmu (coprocessor_instruction <|proc:=0|> (enc,cond,inst)) (assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints priv_mode_similar`;
e(FULL_SIMP_TAC (srw_ss()) [coprocessor_instruction_def]);
e((REPEAT (CASE_TAC)) THEN FULL_SIMP_TAC (srw_ss()) [coprocessor_load_instr_def, coprocessor_store_instr_def, coprocessor_register_to_arm_instr_def, arm_register_to_coprocessor_instr_def, coprocessor_register_to_arm_two_instr_def, arm_register_to_coprocessor_two_instr_def, coprocessor_data_processing_instr_def, LET_DEF]);
go_on_p 7;
val coprocessor_instruction_comb_thm = save_comb_thm("coprocessor_instruction_comb_thm", top_thm(), ``coprocessor_instruction``);

