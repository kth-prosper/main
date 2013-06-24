;

g `preserve_relation_mmu 
  ((current_mode_is_user_or_system <|proc := 0|>
      ||| current_instr_set <|proc := 0|>) >>=
   (λ(is_user_or_system,iset).
      if is_user_or_system ∨ (iset = InstrSet_ThumbEE) then
        errorT "store_return_state_instr: unpredictable"
      else
        (read_reg_mode <|proc := 0|> (13w,c)
           ||| read_reg <|proc := 0|> 14w
           ||| read_spsr <|proc := 0|>) >>=
        (λ(base,lr,spsr).
           (increment_pc <|proc := 0|> enc
              ||| write_memA <|proc := 0|>
                    (if b ⇔ b0 then
                       (if b0 then base else base + 0xFFFFFFF8w) + 4w
                     else if b0 then
                       base
                     else
                       base + 0xFFFFFFF8w,4) (bytes (lr,4))
              ||| write_memA <|proc := 0|>
                    ((if b ⇔ b0 then
                        (if b0 then base else base + 0xFFFFFFF8w) + 4w
                      else if b0 then
                        base
                      else
                        base + 0xFFFFFFF8w) + 4w,4)
                    (bytes (encode_psr spsr,4))
              ||| condT b1
                    (write_reg_mode <|proc := 0|> (13w,c)
                       (if b0 then
                          base + 8w
                        else
                          base + 0xFFFFFFF8w))) >>=
           (λ(u1,u2,u3,u4). return ())))) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints  priv_mode_similar`;
e(FULL_SIMP_TAC (srw_ss()) [user_simp_par_or_eqv_rel_lem]);
go_on 1;
val store_return_state_instr_help_let_thm = save_thm ("store_return_state_instr_help_let_thm", top_thm());


val store_return_state_instr_help_let_comb_thm = store_thm ("store_return_state_instr_help_let_comb_thm",
    ``preserve_relation_mmu 
     ((current_mode_is_user_or_system <|proc := 0|>
      ||| current_instr_set <|proc := 0|>) >>=
   (λ(is_user_or_system,iset).
      if is_user_or_system ∨ (iset = InstrSet_ThumbEE) then
        errorT "store_return_state_instr: unpredictable"
      else
        (read_reg_mode <|proc := 0|> (13w,c)
           ||| read_reg <|proc := 0|> 14w
           ||| read_spsr <|proc := 0|>) >>=
        (λ(base,lr,spsr).
           (increment_pc <|proc := 0|> enc
              ||| write_memA <|proc := 0|>
                    (if b ⇔ b0 then
                       (if b0 then base else base + 0xFFFFFFF8w) + 4w
                     else if b0 then
                       base
                     else
                       base + 0xFFFFFFF8w,4) (bytes (lr,4))
              ||| write_memA <|proc := 0|>
                    ((if b ⇔ b0 then
                        (if b0 then base else base + 0xFFFFFFF8w) + 4w
                      else if b0 then
                        base
                      else
                        base + 0xFFFFFFF8w) + 4w,4)
                    (bytes (encode_psr spsr,4))
              ||| condT b1
                    (write_reg_mode <|proc := 0|> (13w,c)
                       (if b0 then
                          base + 8w
                        else
                          base + 0xFFFFFFF8w))) >>=
           (λ(u1,u2,u3,u4). return ()))))
      (assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints priv_mode_similar``,
     ASSUME_TAC store_return_state_instr_help_let_thm
        THEN ASSUME_TAC (SPECL [``16w:word5``, ``27w:word5``] comb_mode_thm)
        THEN ASSUME_TAC (SPECL [``(assert_mode 16w):(arm_state->bool)``,
                     ``(assert_mode 27w):(arm_state->bool)``,
                     ``(comb_mode 16w 27w):(arm_state->bool)``, 
                     ``(assert_mode 16w):(arm_state->bool)``] (INST_TYPE [alpha |-> type_of(``()``)] preserve_relation_comb_v2_thm))
        THEN RES_TAC);
add_to_simplist store_return_state_instr_help_let_comb_thm;




val store_multiple_part = ``(λ(base,cpsr).
                (let mode = if system then 16w else cpsr.M and
                     length = n2w (4 * bit_count registers) and
                     lowest = lowest_set_bit registers
                 in
                 let base_address = if add then base else base − length
                 in
                 let start_address =
                       if indx ⇔ add then
                         base_address + 4w
                       else
                         base_address
                 in
                 let address i =
                       start_address +
                       n2w (4 * (bit_count_upto (i + 1) registers − 1))
                 in
                   forT 0 14
                     (λi.
                        condT ((registers:word16) ' i)
                          (if (i = w2n n) ∧ wback ∧ i ≠ lowest then
                             write_memA <|proc:=0|> (address i,4) BITS32_UNKNOWN
                           else
                             read_reg_mode <|proc:=0|> (n2w i,mode) >>=
                             (λd.
                                write_memA <|proc:=0|> (address i,4)
                                  (bytes (d,4))))) >>=
                   (λunit_list.
                      (condT (registers ' 15)
                         (pc_store_value <|proc:=0|> >>=
                          (λpc.
                             write_memA <|proc:=0|> (address 15,4)
                               (bytes (pc,4)))) ||| increment_pc <|proc:=0|> enc
                         ||| condT wback
                               (if add then
                                  write_reg <|proc:=0|> n (base + length)
                                else
                                  write_reg <|proc:=0|> n (base − length))) >>=
                      (λ(u1,u2,u3). return ())))):bool[32] # ARMpsr -> unit M``;


val store_multiple_part_simp = store_thm(
    "store_multiple_part_simp",
    `` (preserve_relation_mmu(
         (read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>=
             (λ(base,cpsr).
                (let mode = if system then 16w else cpsr.M and
                     length = n2w (4 * bit_count registers) and
                     lowest = lowest_set_bit registers
                 in
                 let base_address = if add then base else base − length
                 in
                 let start_address =
                       if indx ⇔ add then
                         base_address + 4w
                       else
                         base_address
                 in
                 let address i =
                       start_address +
                       n2w (4 * (bit_count_upto (i + 1) registers − 1))
                 in
                   forT 0 14
                     (λi.
                        condT ((registers:word16) ' i)
                          (if (i = w2n n) ∧ wback ∧ i ≠ lowest then
                             write_memA <|proc:=0|> (address i,4) BITS32_UNKNOWN
                           else
                             read_reg_mode <|proc:=0|> (n2w i,mode) >>=
                             (λd.
                                write_memA <|proc:=0|> (address i,4)
                                  (bytes (d,4))))) >>=
                   (λunit_list.
                      (condT (registers ' 15)
                         (pc_store_value <|proc:=0|> >>=
                          (λpc.
                             write_memA <|proc:=0|> (address 15,4)
                               (bytes (pc,4)))) ||| increment_pc <|proc:=0|> enc
                         ||| condT wback
                               (if add then
                                  write_reg <|proc:=0|> n (base + length)
                                else
                                  write_reg <|proc:=0|> n (base − length))) >>=
                      (λ(u1,u2,u3). return ()))))) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar)
           =
         (preserve_relation_mmu
           ((read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>=
             (λ(base,cpsr).
                (let mode = if system then 16w else 16w and
                     length = n2w (4 * bit_count registers) and
                     lowest = lowest_set_bit registers
                 in
                 let base_address = if add then base else base − length
                 in
                 let start_address =
                       if indx ⇔ add then
                         base_address + 4w
                       else
                         base_address
                 in
                 let address i =
                       start_address +
                       n2w (4 * (bit_count_upto (i + 1) registers − 1))
                 in
                   forT 0 14
                     (λi.
                        condT ((registers:word16) ' i)
                          (if (i = w2n n) ∧ wback ∧ i ≠ lowest then
                             write_memA <|proc:=0|> (address i,4) BITS32_UNKNOWN
                           else
                             read_reg_mode <|proc:=0|> (n2w i,mode) >>=
                             (λd.
                                write_memA <|proc:=0|> (address i,4)
                                  (bytes (d,4))))) >>=
                   (λunit_list.
                      (condT (registers ' 15)
                         (pc_store_value <|proc:=0|> >>=
                          (λpc.
                             write_memA <|proc:=0|> (address 15,4)
                               (bytes (pc,4)))) ||| increment_pc <|proc:=0|> enc
                         ||| condT wback
                               (if add then
                                  write_reg <|proc:=0|> n (base + length)
                                else
                                  write_reg <|proc:=0|> n (base − length))) >>=
                      (λ(u1,u2,u3). return ()))))) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar)``,
    FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def]
       THEN EQ_TAC
       THEN (REPEAT STRIP_TAC)
       THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``n:word4``, store_multiple_part] (INST_TYPE [alpha |-> type_of(``()``)] read_reg_read_cpsr_par_effect_lem))
       THEN ASSUME_TAC (SPECL [``s2:arm_state``, ``n:word4``, store_multiple_part] (INST_TYPE [alpha |-> type_of(``()``)] read_reg_read_cpsr_par_effect_lem))
       THEN RES_TAC
       THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []);




g `!n. preserve_relation_mmu
       ((read_reg <|proc := 0|> n ||| read_cpsr <|proc := 0|>) >>=
        (λ(base,cpsr).
           forT 0 14
             (λi.
                condT ((c0:word16) ' i)
                  (if (i = (w2n n)) ∧ b2 ∧ i ≠ lowest_set_bit c0 then
                     write_memA <|proc := 0|>
                       (n2w (4 * (bit_count_upto (w2n n + 1) c0 − 1)) +
                        if b ⇔ b0 then
                          (if b0 then
                             base
                           else
                             base + -1w * n2w (4 * bit_count c0)) + 4w
                        else if b0 then
                          base
                        else
                          base + -1w * n2w (4 * bit_count c0),4)
                       BITS32_UNKNOWN
                   else
                     read_reg_mode <|proc := 0|>
                       (n2w i,if b1 then 16w else cpsr.M) >>=
                     (λd.
                        write_memA <|proc := 0|>
                          (n2w (4 * (bit_count_upto (i + 1) c0 − 1)) +
                           if b ⇔ b0 then
                             (if b0 then
                                base
                              else
                                base + -1w * n2w (4 * bit_count c0)) +
                             4w
                           else if b0 then
                             base
                           else
                             base + -1w * n2w (4 * bit_count c0),4)
                          (bytes (d,4))))) >>=
           (λunit_list.
              (condT (c0 ' 15)
                 (pc_store_value <|proc := 0|> >>=
                  (λpc.
                     write_memA <|proc := 0|>
                       (n2w (4 * (bit_count_upto 16 c0 − 1)) +
                        if b ⇔ b0 then
                          (if b0 then
                             base
                           else
                             base + -1w * n2w (4 * bit_count c0)) + 4w
                        else if b0 then
                          base
                        else
                          base + -1w * n2w (4 * bit_count c0),4)
                       (bytes (pc,4))))
                 ||| increment_pc <|proc := 0|> enc
                 ||| condT b2
                       (if b0 then
                          write_reg <|proc := 0|> n
                            (base + n2w (4 * bit_count c0))
                        else
                          write_reg <|proc := 0|> n
                            (base + -1w * n2w (4 * bit_count c0)))) >>=
              (λ(u1,u2,u3). return ())))) (assert_mode 16w)  (assert_mode 16w) priv_mode_constraints priv_mode_similar`;
e(STRIP_TAC);
e(ASSUME_TAC (SPECL [``b2:bool``, ``b1:bool``, ``c0:word16``, ``n:word4``, ``b:bool``, ``enc:Encoding``, ``b0:bool``] (GEN_ALL store_multiple_part_simp)));
e(FULL_SIMP_TAC (srw_ss()) [LET_DEF]);
go_on 1;
val store_multiple_part_thm = save_thm ("store_multiple_part_thm", top_thm());
val store_multiple_part_thm_n = save_thm ("store_multiple_part_thm_n", (SPEC ``n:word4`` store_multiple_part_thm));
val store_multiple_part_thm_13 = save_thm ("store_multiple_part_thm_13", (SIMP_RULE (srw_ss()) [] (SPEC ``13w:word4`` store_multiple_part_thm)));
val store_multiple_part_thm_15 = save_thm ("store_multiple_part_thm_15", (SIMP_RULE (srw_ss()) [] (SPEC ``15w:word4`` store_multiple_part_thm)));

add_to_simplist store_multiple_part_thm;
add_to_simplist store_multiple_part_thm_n;
add_to_simplist store_multiple_part_thm_13;
add_to_simplist store_multiple_part_thm_15;


val load_multiple_part = 
      ``(λ(base,cpsr).
           forT 0 14
             (λi.
                condT (c0 ' i)
                  (read_memA <|proc := 0|>
                     (n2w (4 * (bit_count_upto (i + 1) c0 − 1)) +
                      if b ⇔ b0 then
                        (if b0 then
                           base
                         else
                           base + -1w * n2w (4 * bit_count c0)) + 4w
                      else if b0 then
                        base
                      else
                        base + -1w * n2w (4 * bit_count c0),4) >>=
                   (λd.
                      write_reg_mode <|proc := 0|>
                        (n2w i,if b1 ∧ ¬c0 ' 15 then 16w else cpsr.M)
                        (word32 d)))) >>=
           (λunit_list.
              condT b2
                (if (¬(c0:word16) ' (w2n n)) then
                   if b0 then
                     write_reg <|proc := 0|> n
                       (base + n2w (4 * bit_count c0))
                   else
                     write_reg <|proc := 0|> n
                       (base + -1w * n2w (4 * bit_count c0))
                 else
                   write_reg <|proc := 0|> n UNKNOWN) >>=
              (λu.
                 if c0 ' 15 then
                   read_memA <|proc := 0|>
                     (n2w (4 * (bit_count_upto 16 c0 − 1)) +
                      if b ⇔ b0 then
                        (if b0 then
                           base
                         else
                           base + -1w * n2w (4 * bit_count c0)) + 4w
                      else if b0 then
                        base
                      else
                        base + -1w * n2w (4 * bit_count c0),4) >>=
                   (λd.
                      if b1 then
                        current_mode_is_user_or_system <|proc := 0|> >>=
                        (λis_user_or_system.
                           if is_user_or_system then
                             errorT "load_multiple_instr: unpredictable"
                           else
                             read_spsr <|proc := 0|> >>=
                             (λspsr.
                                cpsr_write_by_instr <|proc := 0|>
                                  (encode_psr spsr,15w,T) >>=
                                (λu.
                                   branch_write_pc <|proc := 0|>
                                     (word32 d))))
                      else
                        load_write_pc <|proc := 0|> (word32 d))
                 else
                   increment_pc <|proc := 0|> enc))):(word32 # ARMpsr -> unit M)``;


g `!n. preserve_relation_mmu
       ((read_reg <|proc := 0|> n ||| read_cpsr <|proc := 0|>) >>= (^load_multiple_part)) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar`;
e(STRIP_TAC);
e(ASSUME_TAC (SPECL [``n:word4``, load_multiple_part, ``(assert_mode 16w)``, ``priv_mode_constraints``, ``priv_mode_similar``] (INST_TYPE [alpha |-> Type `:unit`] cpsr_par_simp_rel_lem)));
e(FULL_SIMP_TAC (srw_ss()) []);
go_on 1;
val load_multiple_part_thm = top_thm();
val load_multiple_part_thm_13 = save_thm ("load_multiple_part_thm_13", (SIMP_RULE (srw_ss()) [] (SPEC ``13w:word4`` load_multiple_part_thm)));
val load_multiple_part_thm_15 = save_thm ("load_multiple_part_thm_15", (SIMP_RULE (srw_ss()) [] (SPEC ``15w:word4`` load_multiple_part_thm)));
add_to_simplist load_multiple_part_thm;
add_to_simplist load_multiple_part_thm_13;
add_to_simplist load_multiple_part_thm_15;

  


g `preserve_relation_mmu (load_store_instruction <|proc:=0|> (enc,inst))(assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints priv_mode_similar`;
e(FULL_SIMP_TAC (srw_ss()) [load_store_instruction_def]);
e(Cases_on `inst` THEN FULL_SIMP_TAC (srw_ss()) []);
(* load *)
go_on_p 1;
(* store *)
go_on_p 1;
(* load halfword *)
go_on_p 1;
(* store halfword *)
go_on_p 1;
(* load dual *)
go_on_p 1;
(* store dual *)
go_on_p 1;
(* load multiple *)
go_on_p 1;
(* store multiple *)
go_on_p 1;
(* load exclusive *)
go_on_p 1;
(* store exclusive *)
go_on_p 1;
(* load exclusive doubleword *)
go_on_p 1;
(* store exclusive doubleword *)
go_on_p 1;
(* load exclusive halfword *)
go_on_p 1;
(* store exclusive halfword *)
go_on_p 1;
(* load exclusive byte *)
go_on_p 1;
(* store exclusive byte *)
go_on_p 1;
(* store return state *)
e(FULL_SIMP_TAC (srw_ss()) [store_return_state_instr_def, instruction_def, run_instruction_def, LET_DEF]);
go_on_p 1;
(* return from exception *)
go_on_p 1;
val load_store_instruction_comb_thm = save_comb_thm("load_store_instruction_comb_thm", top_thm(), ``load_store_instruction``);



