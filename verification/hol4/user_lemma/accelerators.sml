;


val increment_pc_thm = prove_and_save_e (``increment_pc <|proc:=0|> enc``, "increment_pc_thm");


val load_write_pc_thm = prove_and_save_e (``load_write_pc <|proc:=0|> add``, "load_write_pc_thm");

val alu_write_pc_thm = prove_and_save_e (``alu_write_pc <|proc:=0|> add``, "alu_write_pc_thm");

val arm_expand_imm_thm = prove_and_save_e (``arm_expand_imm <|proc:=0|> imm12``, "arm_expand_imm_thm");

val shift_thm = prove_and_save_e (``shift (value, type, amount, carry_in)``, "shift_thm");

val read_flags_thm = prove_and_save_e (``read_flags <|proc:=0|>``, "read_flags_thm");


val read_memU_thm = prove_and_save_e (``read_memU <|proc:=0|> (add, n)``, "read_memU_thm");

val read_memU_unpriv_thm = prove_and_save_e (``read_memU_unpriv <|proc:=0|> (add, n)``, "read_memU_unpriv_thm");

val read_memA_thm = prove_and_save_s (``read_memA <|proc:=0|> (add, n)``, "read_memA_thm");

val write_memU_thm = prove_and_save_e (``write_memU <|proc:=0|> (add, n) x``, "write_memU_thm");

val write_memU_unpriv_thm = prove_and_save_e (``write_memU_unpriv <|proc:=0|> (add, n) x``, "write_memU_unpriv_thm");

val write_memA_thm = prove_and_save_e (``write_memA <|proc:=0|> (add, n) x``, "write_memA_thm");

val read_reg_literal_thm = prove_and_save_e (``read_reg_literal <|proc:=0|> n``, "read_reg_literal_thm");

val big_endian_thm = prove_and_save_s (``big_endian <|proc:=0|>``, "big_endian_thm");

val unaligned_support_thm = prove_and_save_e (``unaligned_support <|proc:=0|>``, "unaligned_support_thm");

val pc_store_value_thm = prove_and_save_e (``pc_store_value <|proc:=0|>``, "pc_store_value_thm");

val is_secure_thm = prove_and_save_e(``is_secure <|proc:=0|>``, "is_secure_thm");

val read_nsacr_thm = prove_and_save_e(``read_nsacr <|proc:=0|>``, "read_nsacr_thm");

val current_instr_set_thm = prove_and_save_s(``current_instr_set <|proc:=0|>``, "current_instr_set_thm");

val branch_write_pc_thm = prove_and_save_e(``branch_write_pc <|proc:=0|> d``, "branch_write_pc_thm");

val no_operation_instr_comb_thm = prove_and_save_p (``no_operation_instr <|proc := 0|> enc``, "no_operation_instr_comb_thm", ``no_operation_instr``);



