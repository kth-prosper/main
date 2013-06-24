;

(* write flags for triples *)

g `preserve_relation_mmu (write_flags <|proc := 0|>  (a,b,c)) (assert_mode 16w)  (assert_mode 16w) priv_mode_constraints priv_mode_similar`;
e(pairLib.PairCases_on `c`);
go_on 1;
val write_flags_triple_thm = top_thm();
add_to_simplist write_flags_triple_thm;

(* data processing instr *)

val data_processing_pre_part = ``((if ((c:word4) = 13w) ∨ (c = 15w) ∧ (enc ≠ Encoding_Thumb2 ∨ (c0 = 15w)) then
            return 0w
          else
            read_reg <|proc := 0|> c0)
           ||| address_mode1 <|proc := 0|> (enc = Encoding_Thumb2) a
           ||| read_flags <|proc := 0|>)
   : ((word32 # (word32 # bool) # bool # bool #bool # bool) M)``;
val data_processing_pre_part_thm = prove_and_save_e(``^data_processing_pre_part``, "data_processing_pre_part_thm");


val data_processing_core_part = ``(λ((rn :bool[32]),((shifted :bool[32]),(C_shift :bool)),(N :bool),
     (Z :bool),(C :bool),(V :bool)).
     ((if ((3 :num) -- (2 :num)) (c :bool[4]) = (2w :bool[4]) then
         increment_pc <|proc := (0 :num)|> enc
       else if (c1 :bool[4]) = (15w :bool[4]) then
         if (b :bool) then
           read_spsr <|proc := (0 :num)|> >>=
           (λ(spsr :ARMpsr).
              cpsr_write_by_instr <|proc := (0 :num)|>
                (encode_psr spsr,(15w :bool[4]),T) >>=
              (λ(u :unit).
                 branch_write_pc <|proc := (0 :num)|>
                   (FST (data_processing_alu c rn shifted C))))
         else
           alu_write_pc <|proc := (0 :num)|>
             (FST (data_processing_alu c rn shifted C))
       else
         (increment_pc <|proc := (0 :num)|> enc
            ||| write_reg <|proc := (0 :num)|> c1
                  (FST (data_processing_alu c rn shifted C))) >>=
         (λ((u1 :unit),(u2 :unit)). return ()))
        ||| if
              b ∧
              (c1 ≠ (15w :bool[4]) ∨
               (((3 :num) -- (2 :num)) c = (2w :bool[4])))
            then
              if
                (c ' (2 :num) ∨ c ' (1 :num)) ∧
                (¬c ' (3 :num) ∨ ¬c ' (2 :num))
              then
                write_flags <|proc := (0 :num)|>
                  (word_msb (FST (data_processing_alu c rn shifted C)),
                   FST (data_processing_alu c rn shifted C) =
                   (0w
                     :bool[32]),
                   SND (data_processing_alu c rn shifted C))
              else
                write_flags <|proc := (0 :num)|>
                  (word_msb (FST (data_processing_alu c rn shifted C)),
                   FST (data_processing_alu c rn shifted C) =
                   (0w
                     :bool[32]),C_shift,V)
            else
              return ()) >>= (λ((u1 :unit),(u2 :unit)). return ())):(word32 # (word32 # bool) # bool # bool #bool # bool -> unit M)``;

g `∀y. preserve_relation_mmu(^data_processing_core_part y) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints priv_mode_similar`;
e(STRIP_TAC);
e(pairLib.PairCases_on `y`);
e(FULL_SIMP_TAC (srw_ss()) []);
go_on 1;
val data_processing_core_part_thm1 = top_thm();
val data_processing_core_part_thm2 = SIMP_RULE (srw_ss()) [(SPECL [data_processing_core_part, ``(assert_mode 16w):(arm_state->bool)``, ``(assert_mode 16w):(arm_state->bool)``] (INST_TYPE [alpha |-> (Type `:(word32 # (word32 # bool) # bool # bool #bool # bool)`), beta |-> type_of (``()``)] second_abs_lemma))] data_processing_core_part_thm1;
add_to_simplist data_processing_core_part_thm2;


g `preserve_relation_mmu ((^data_processing_pre_part) >>= (^data_processing_core_part)) (assert_mode 16w) (comb_mode 16w 27w)  priv_mode_constraints priv_mode_similar`;
e(FULL_SIMP_TAC (srw_ss()) [seqT_preserves_relation_uu_thm, comb_monot_thm, data_processing_core_part_thm2, data_processing_pre_part_thm, trans_priv_mode_constraints_thm]);
e(ASSUME_TAC data_processing_core_part_thm2);
e(ASSUME_TAC data_processing_pre_part_thm);
e(ASSUME_TAC (SPEC ``(assert_mode 16w):(arm_state->bool)`` comb_monot_thm));
e(ASSUME_TAC (SPECL [data_processing_pre_part, data_processing_core_part,``16w:word5``, ``priv_mode_constraints``, ``priv_mode_similar``]  (INST_TYPE [alpha |-> Type `:(word32 # (word32 # bool) # bool # bool #bool # bool)`, beta |-> type_of (``()``)] seqT_preserves_relation_uu_thm)));
e(FULL_SIMP_TAC (srw_ss()) [preserve_relation_comb_16_27_thm, trans_priv_mode_constraints_thm]);
val data_processing_help_thm = top_thm();
add_to_simplist data_processing_help_thm;

(* multiply long - write flags - part *)

val multiply_long_instr_part_thm = store_thm(
    "multiply_long_instr_part_thm",
    ``preserve_relation_mmu
      ((λ(C_flag,V_flag).
      write_flags <|proc := 0|>
        (word_msb
           ((if b then sw2sw rm * sw2sw rn else w2w rm * w2w rn) +
            if b0 then rdhi @@ rdlo else 0w),
         (if b then sw2sw rm * sw2sw rn else w2w rm * w2w rn) +
         (if b0 then rdhi @@ rdlo else 0w) =
         0w,C_flag,V_flag))
      (if version = 4 then (UNKNOWN,UNKNOWN) else (C,V)))
      (assert_mode 16w) (assert_mode 16w) priv_mode_constraints
     priv_mode_similar``,
    RW_TAC (srw_ss()) [(GEN_ALL write_flags_thm)]);
add_to_simplist multiply_long_instr_part_thm;

(* instructions *)

g `preserve_relation_mmu (data_processing_instruction <|proc := 0|> (enc,inst)) (assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints priv_mode_similar`;
e (Cases_on `inst` THEN FULL_SIMP_TAC (srw_ss()) []);
(*30 subgoals *)
(* data processing *) 
e(FULL_SIMP_TAC (srw_ss()) [data_processing_instruction_def, data_processing_instr, LET_DEF] THEN PairedLambda.GEN_BETA_TAC);
e(Q.ABBREV_TAC `xx = (shifted, C_shift)`);
go_on_p 1;
(* add sub *)
go_on_p 1; 
(* move halfword  *)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* multiply*)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* multiply subtract *)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* signed halword multiply *)
e(FULL_SIMP_TAC (srw_ss()) [data_processing_instruction_def]);
e(Cases_on `enc` THEN Cases_on `c=0w` THEN Cases_on `c=1w` THEN Cases_on `b0` THEN Cases_on `c=2w` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 32;
(* signed multiply dual *)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* signed multiply long dual *)
go_on_p 1;
(* signed most significant multiply *)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* signed most significant multiply subtract *)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* multiply long *)
go_on_p 1;
(* multiply accumulate accumulate *)
go_on_p 1;
(* saturate *)
e(FULL_SIMP_TAC (srw_ss()) [data_processing_instruction_def, saturate_instr, LET_DEF] THEN REPEAT CASE_TAC THEN PairedLambda.GEN_BETA_TAC);
go_on_p 8;
(* saturate 16 *)
e(FULL_SIMP_TAC (srw_ss()) [data_processing_instruction_def, saturate_16_instr, LET_DEF] THEN REPEAT CASE_TAC THEN PairedLambda.GEN_BETA_TAC);
go_on_p 8;
(* saturating add subtract *)
e(FULL_SIMP_TAC (srw_ss()) [data_processing_instruction_def, saturating_add_subtract_instr, LET_DEF] THEN Cases_on `enc` THEN PairedLambda.GEN_BETA_TAC THEN  FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* pack halfword *)
e (FULL_SIMP_TAC (srw_ss()) [data_processing_instruction_def, pack_halfword_instr_def]);
e (Cases_on `decode_imm_shift ((1 :+ b) 0w,c1)` THEN FULL_SIMP_TAC (srw_ss()) []);
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* extend byte *)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* extend_byte_16 *)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* extend halword *)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* bit field clear insert *)
go_on_p 1;
(* count leading zeroes *)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* reverse bits *)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* byte reverse word *)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* byte reverse packed halfword *)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* byte reverse signed halword *)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* bit field extract *)
go_on_p 1;
(* select bytes *)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* unsigned sum absolute differences *)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* parallel add subtract *)
e(Cases_on `enc` THEN FULL_SIMP_TAC (srw_ss()) [data_processing_instruction_def, parallel_add_subtract_instr, LET_DEF] THEN PairedLambda.GEN_BETA_TAC THEN FULL_SIMP_TAC (srw_ss()) []);
go_on_p 4;
(* divide *)
go_on_p 1;
(* now save *)
val data_processing_instruction_comb_thm = save_comb_thm("data_processing_instruction_comb_thm", top_thm(), ``data_processing_instruction``);


