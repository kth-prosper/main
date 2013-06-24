;

g `preserve_relation_mmu (status_access_instruction <|proc:=0|> (enc, inst)) (assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints priv_mode_similar`;
e (Cases_on `inst` THEN FULL_SIMP_TAC (srw_ss()) []);
(* status to register *)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on 4;
(* register to status *)
go_on 1;
(* immediate to status *)
go_on 1;
(* change processor state *)
go_on 1;
(* set endianness *)
go_on 1;
val status_access_instruction_comb_thm = save_comb_thm ("status_access_instruction_comb_thm", top_thm(), ``status_access_instruction``);



