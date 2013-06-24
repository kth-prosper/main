;

val mode_mix_def = Define `mode_mix = (\s. (ARM_MODE s = 16w) \/ (ARM_MODE s = 17w) \/ (ARM_MODE s = 18w) \/ (ARM_MODE s = 27w) \/ (ARM_MODE s = 23w) \/ (ARM_MODE s = 19w))`;

val little_mode_mix_def = Define `little_mode_mix = (\s. (ARM_MODE s = 16w) \/  (ARM_MODE s = 17w) \/ (ARM_MODE s = 18w) \/ (ARM_MODE s = 27w) \/ (ARM_MODE s = 23w))`;


val pmc_12_upgrade = store_thm(
    "pmc_12_upgrade",
    ``!g s t. (ARM_MODE t <> 19w) ==> (priv_mode_constraints_v1 g s t = priv_mode_constraints_v2 g s t)``,
    RW_TAC (srw_ss()) [priv_mode_constraints_v2_def]);


val little_mode_mix_upgrade = store_thm(
    "little_mode_mix_upgrade",
    ``!A inv1 uf uy.
      (   preserve_relation_mmu (A) inv1 (assert_mode 16w)   uf uy
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 27w) uf uy 	
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 23w) uf uy
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 17w) uf uy
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 18w) uf uy)	
       ==>
          preserve_relation_mmu (A) inv1 little_mode_mix uf uy``,
    RW_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, comb_mode_def, little_mode_mix_def]
       THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
       THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) [little_mode_mix_def]);

val mode_mix_upgrade = store_thm(
    "mode_mix_upgrade",
    ``!A inv1.
      (   preserve_relation_mmu (A) inv1 (assert_mode 16w)   priv_mode_constraints_v1 priv_mode_similar
       \/ preserve_relation_mmu (A) inv1 little_mode_mix     priv_mode_constraints_v1 priv_mode_similar
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 27w) priv_mode_constraints_v1 priv_mode_similar
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 23w) priv_mode_constraints_v1 priv_mode_similar
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 19w) priv_mode_constraints_v2 priv_mode_similar
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 17w) priv_mode_constraints_v1 priv_mode_similar
       \/ preserve_relation_mmu (A) inv1 (comb_mode 16w 18w) priv_mode_constraints_v1 priv_mode_similar)
       ==>
          preserve_relation_mmu (A) inv1 mode_mix priv_mode_constraints_v2 priv_mode_similar``,
    RW_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, comb_mode_def, mode_mix_def, pmc_12_upgrade, little_mode_mix_def]
       THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
       THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) [pmc_12_upgrade]);


val mode_mix_const_upgrade = store_thm(
    "mode_mix_const_upgrade",
    ``!A uf uy.
          (!k. preserve_relation_mmu (A) (assert_mode k) (assert_mode k) uf uy)
       ==>
          preserve_relation_mmu (A) mode_mix mode_mix uf uy``,
    RW_TAC (srw_ss()) [preserve_relation_mmu_def, assert_mode_def, comb_mode_def, mode_mix_def]
       THEN `(similar g s1 s2) ==> (ARM_MODE s1 = ARM_MODE s2)` by
            EVAL_TAC
               THEN RW_TAC (srw_ss()) []
               THEN SPEC_ASSUM_TAC (``!(ii:iiid). X``, [``<|proc:=0|>``])
               THEN FULL_SIMP_TAC (srw_ss()) []
       THEN RW_TAC (srw_ss()) []
       THEN METIS_TAC []);

val mode_mix_comb_16_thm = store_thm(
    "mode_mix_comb_16_thm",
    ``comb (assert_mode 16w) mode_mix mode_mix``,
    EVAL_TAC THEN RW_TAC (srw_ss()) [] THEN METIS_TAC []);


val little_mode_mix_comb_16_thm = store_thm(
    "little_mode_mix_comb_16_thm",
    ``comb (assert_mode 16w) little_mode_mix little_mode_mix``,
    EVAL_TAC THEN RW_TAC (srw_ss()) [] THEN METIS_TAC []);


fun MODE_MIX_TAC newtrg (assumptions, gl) =
            case (dest_term gl) of
                COMB (rcstu, sim)
                => case dest_term rcstu of
                     COMB (rcst, unt)
                     => case dest_term rcst of 
                            COMB (rcs, i2)
                            => case (dest_term rcs) of 
                                   COMB (rc, i1) => 
                                        case (dest_term rc) of
                                             COMB (rel, comp)  => if ((i2 = ``mode_mix:(arm_state->bool)``) andalso ((unt = ``priv_mode_constraints_v2``) andalso (sim=``priv_mode_similar``)))
                                                                  then ((SUBGOAL_THEN (mk_comb(mk_comb((mk_comb(rcs, newtrg)), (if (newtrg = ``comb_mode 16w 19w``) then ``priv_mode_constraints_v2`` else ``priv_mode_constraints_v1``)), sim)) (fn thm => RW_TAC (srw_ss()) [thm, mode_mix_upgrade])) (assumptions, gl))
                                                                 else (ALL_TAC (assumptions, gl))
                                             | _ => (ALL_TAC (assumptions, gl))
                               | _ => (ALL_TAC (assumptions, gl))
                        | _ => (ALL_TAC (assumptions, gl))
                   | _ => (ALL_TAC (assumptions, gl))
              | _ => (ALL_TAC (assumptions, gl));


fun LITTLE_MODE_MIX_TAC newtrg (assumptions, gl) =
            case (dest_term gl) of
                COMB (rcstu, sim)
                => case dest_term rcstu of
                     COMB (rcst, unt)
                     => case dest_term rcst of 
                            COMB (rcs, i2)
                            => case (dest_term rcs) of 
                                   COMB (rc, i1) => 
                                        case (dest_term rc) of
                                             COMB (rel, comp)  => if (i2 = ``little_mode_mix:(arm_state->bool)``)
                                                                  then ((SUBGOAL_THEN (mk_comb(mk_comb((mk_comb(rcs, newtrg)),unt), sim)) (fn thm => RW_TAC (srw_ss()) [thm, little_mode_mix_upgrade])) (assumptions, gl))
                                                                 else (ALL_TAC (assumptions, gl))
                                             | _ => (ALL_TAC (assumptions, gl))
                               | _ => (ALL_TAC (assumptions, gl))
                        | _ => (ALL_TAC (assumptions, gl))
                   | _ => (ALL_TAC (assumptions, gl)) 
              | _ => (ALL_TAC (assumptions, gl));





val read_info_constlem = store_thm(
    "read_info_constlem",
    ``!s. ?x. ((read_info <|proc:=0|>) s) = ValueState x s``,
    RW_TAC (srw_ss()) [read_info_def, readT_def]);


val read_info_thm = prove_and_save_e(``read_info <|proc:=0|>``, "read_info_thm");



g `preserve_relation_mmu (miscellaneous_instruction <|proc:=0|> (enc,inst)) (assert_mode 16w) mode_mix priv_mode_constraints_v2 priv_mode_similar`;
e(FULL_SIMP_TAC (srw_ss()) [miscellaneous_instruction_def]);
e(REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) []));
(* NOP *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
go_on_p 1;
(* yield *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
e(Cases_on `enc = Encoding_ARM` THEN FULL_SIMP_TAC (srw_ss()) [yield_instr, hint_yield_def]);
go_on_p 2;
(* wait for event *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
e(Cases_on `enc = Encoding_ARM` THEN FULL_SIMP_TAC (srw_ss()) [wait_for_event_instr_def, instruction_def, run_instruction_def]);
go_on_p 2;
(* wait for interrupt *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
e(Cases_on `enc = Encoding_ARM` THEN FULL_SIMP_TAC (srw_ss()) [wait_for_interrupt_instr_def, instruction_def, run_instruction_def]);
go_on_p 2;
(* send event *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
e(Cases_on `enc = Encoding_ARM` THEN FULL_SIMP_TAC (srw_ss()) [send_event_instr_def, instruction_def, run_instruction_def]);
go_on_p 2;
(* debug *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
e(Cases_on `enc = Encoding_ARM` THEN FULL_SIMP_TAC (srw_ss()) [debug_instr_def, instruction_def, run_instruction_def]);
go_on_p 2;
(* breakpoint *)
e(MODE_MIX_TAC ``little_mode_mix``);
e(FULL_SIMP_TAC (srw_ss()) [breakpoint_instr]);
e(SUBGOAL_THEN ``!info. preserve_relation_mmu (if version_number info.arch < 5 then take_undef_instr_exception <|proc := 0|> else take_prefetch_abort_exception <|proc := 0|>) (assert_mode 16w) little_mode_mix priv_mode_constraints_v1 priv_mode_similar`` 
  (fn th => ASSUME_TAC th 
       THEN ASSUME_TAC (SPEC ``(λinfo. if version_number info.arch < 5 then take_undef_instr_exception <|proc := 0|> else take_prefetch_abort_exception <|proc := 0|>)`` (INST_TYPE [alpha |-> Type `:ARMinfo`, beta |-> Type `:unit`]  second_abs_lemma))
       THEN ASSUME_TAC trans_priv_mode_constraints_thm
       THEN ASSUME_TAC (SPECL [``(read_info <|proc:=0|>):(ARMinfo M)``, ``( \info. (if version_number info.arch < 5 then take_undef_instr_exception <|proc := 0|> else take_prefetch_abort_exception <|proc := 0|>))``, ``16w:word5``, ``little_mode_mix``, ``little_mode_mix``, ``priv_mode_constraints_v1``, ``priv_mode_similar``] (INST_TYPE [alpha |-> Type `:ARMinfo`, beta |-> Type `:unit`] seqT_preserves_relation_comb_thm))
       THEN FULL_SIMP_TAC (srw_ss()) [little_mode_mix_comb_16_thm, (CONJUNCT1 (CONJUNCT2 read_info_thm))]));
e(STRIP_TAC);
e(CASE_TAC);
e(LITTLE_MODE_MIX_TAC ``comb_mode 16w 27w``);
e(FULL_SIMP_TAC (srw_ss()) [take_undef_instr_exception_comb_thm]);
e(LITTLE_MODE_MIX_TAC ``comb_mode 16w 23w``);
e(FULL_SIMP_TAC (srw_ss()) [take_prefetch_abort_exception_comb_thm]);
(* data memory barrier *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
go_on_p 1;
(* data synch barrier *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
go_on_p 1;
(* inst synch barrier *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
go_on_p 1;
(* swap *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
go_on_p 1;
(* preload data *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
go_on_p 1;
(* preload instr *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
go_on_p 1;
(* svc *)
e(MODE_MIX_TAC ``comb_mode 16w 19w``);
e(FULL_SIMP_TAC (srw_ss()) [take_svc_exception_comb_thm]);
(* secure monitor call *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
go_on_p 1;
(* enter x leave x *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
go_on_p 1;
(* clear exclusive *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
e(FULL_SIMP_TAC (srw_ss()) [clear_exclusive_instr_def, clear_exclusive_local_def, LET_DEF]);
go_on_p 1;
(* if-then *)
e(MODE_MIX_TAC ``comb_mode 16w 27w``);
go_on_p 1;
val miscellaneous_instruction_comb_thm = save_comb_thm("miscellaneous_instruction_comb_thm", top_thm(), ``miscellaneous_instruction``);


