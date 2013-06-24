;


g `preserve_relation_mmu (branch_link_exchange_imm_instr <|proc := 0|>  e  (Branch_Link_Exchange_Immediate b b0 c)) (assert_mode 16w) (comb_mode 16w 27w)  priv_mode_constraints  priv_mode_similar`;
e(Cases_on `b0` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on 1;
e(Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on 4;
val branch_link_exchange_imm_instr_comb_thm = save_comb_thm("branch_link_exchange_imm_instr_comb_thm", top_thm(), ``branch_link_exchange_imm_instr``);



g `preserve_relation_mmu (branch_instruction <|proc := 0|> (e,i)) (assert_mode 16w) (comb_mode 16w 27w)  priv_mode_constraints  priv_mode_similar`;
e(FULL_SIMP_TAC (srw_ss()) [branch_instruction_def]);
e(Cases_on `i` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on 10;
val branch_instruction_comb_thm = save_comb_thm("branch_instruction_comb_thm", top_thm(), ``branch_instruction``);










