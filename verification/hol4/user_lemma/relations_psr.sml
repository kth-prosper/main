(**************  basic operations **********************)

val read_cpsr_thm = prove_and_save_s(``read_cpsr <|proc:=0|>``, "read_cpsr_thm");

(*
val read_cpsr_empty_thm = store_thm("read_cpsr_empty_thm",
  ``!uy . preserve_relation_mmu (read_cpsr <|proc:=0|>) (assert_mode 16w) (assert_mode 16w) empty_unt uy``,
 (RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def, assert_mode_def,read_cpsr_def,read__psr_def,readT_def,untouched_def, priv_mode_constraints_def, empty_unt_def] THEN FULL_SIMP_TAC (srw_ss()) []));


val read_cpsr_pmc_thm = store_thm("read_cpsr_pmc_thm",
  ``!uy . preserve_relation_mmu (read_cpsr <|proc:=0|>) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints uy``,
 (RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def, assert_mode_def,read_cpsr_def,read__psr_def,readT_def,untouched_def, priv_mode_constraints_def] THEN FULL_SIMP_TAC (srw_ss()) []));

val read_cpsr_thm = save_thm("read_cpsr_thm", CONJ read_cpsr_empty_thm read_cpsr_pmc_thm);
*)


val read_cpsr_abs_thm = store_thm("read_cpsr_abs_thm",
  ``!uy. preserve_relation_mmu_abs (\cp. read_cpsr <|proc:=0|>) (assert_mode 16w) (assert_mode 16w) priv_mode_constraints uy``,
 (RW_TAC (srw_ss()) [preserve_relation_mmu_abs_def,similar_def, assert_mode_def, priv_mode_constraints_def, read_cpsr_def,read__psr_def,readT_def,untouched_def] THEN FULL_SIMP_TAC (srw_ss()) []));


val read_cpsr_comb_thm = store_thm("read_cpsr_comb_thm",
  ``!invr uy. preserve_relation_mmu (read_cpsr <|proc:=0|>) invr invr empty_unt uy``,
 (RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def, assert_mode_def,read_cpsr_def,read__psr_def,readT_def,untouched_def, empty_unt_def] THEN FULL_SIMP_TAC (srw_ss()) []));


val write_cpsr_thm = store_thm(
    "write_cpsr_thm",
    `` !k k'. preserve_relation_mmu ( write_cpsr <|proc :=0 |> (cpsr with <|I := xI; F := xF; M := k'|>)) (assert_mode k) (assert_mode k') empty_unt (fix_flags xI xF empty_sim)``,
   `!psr. (psr <> CPSR) ==> (0 <> PSRName2num psr)` by (EVAL_TAC THEN RW_TAC (srw_ss()) [])
      THEN RW_TAC (srw_ss()) [preserve_relation_mmu_def,write_cpsr_def,write__psr_def,writeT_def,similar_def,read_mode_def,untouched_def,assert_mode_def, fix_flags_def, fixed_flags_def, empty_sim_def, empty_unt_def] 
      THEN EVAL_TAC 
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN FULL_SIMP_TAC (srw_ss()) [equal_user_register_def]
      THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``s1 with psrs updated_by ((0,CPSR) =+ cpsr with <|I := xI; F := (s2.psrs (0,CPSR)).F; M := k'|>)``, ``g:word32``]  trivially_untouched_av_lem)
      THEN ASSUME_TAC (SPECL [``s2:arm_state``, ``s2 with psrs updated_by ((0,CPSR) =+ cpsr with <|I := xI; F := (s2.psrs (0,CPSR)).F; M := k'|>)``, ``g:word32``]  trivially_untouched_av_lem)
      THEN UNDISCH_ALL_TAC 
      THEN RW_TAC (srw_ss()) []);



(* write cpsr with several components*)


val write_cpsr_E_IFM_thm = store_thm(
    "write_cpsr_E_IFM_thm",
    ``preserve_relation_mmu (write_cpsr <|proc := 0|> (cpsr with <|E := something; I := xI; F := xF; M := 16w|>)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)``,
    Q.ABBREV_TAC `cpsr2 = (cpsr with E := something)`
      THEN `cpsr with <|E := something; M := 16w; I := xI; F := xF|> = (cpsr2) with <|M := 16w; I := xI; F := xF|>` by Q.UNABBREV_TAC `cpsr2`
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN FULL_SIMP_TAC (srw_ss()) [write_cpsr_thm]);
add_to_simplist  write_cpsr_E_IFM_thm;

val write_cpsr_IT_IFM_thm = store_thm(
    "write_cpsr_IT_IFM_thm",
    ``preserve_relation_mmu (write_cpsr <|proc := 0|> (cpsr with <|IT := something; I := xI; F := xF; M := 16w|>)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)``,
    Q.ABBREV_TAC `cpsr2 = (cpsr with IT := something)`
      THEN `cpsr with <|IT := something; M := 16w; I := xI; F := xF|> = (cpsr2) with <|M := 16w; I := xI; F := xF|>` by Q.UNABBREV_TAC `cpsr2`
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN FULL_SIMP_TAC (srw_ss()) [write_cpsr_thm]);
add_to_simplist  write_cpsr_IT_IFM_thm;


val write_cpsr_GE_IFM_thm = store_thm(
    "write_cpsr_GE_IFM_thm",
    ``preserve_relation_mmu (write_cpsr <|proc := 0|> (cpsr with <|GE := something; I := xI; F := xF; M := 16w|>)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)``,
    Q.ABBREV_TAC `cpsr2 = (cpsr with GE := something)`
      THEN `cpsr with <|GE := something; M := 16w; I := xI; F := xF|> = (cpsr2) with <|M := 16w; I := xI; F := xF|>` by Q.UNABBREV_TAC `cpsr2`
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN FULL_SIMP_TAC (srw_ss()) [write_cpsr_thm]);
add_to_simplist  write_cpsr_GE_IFM_thm;


val write_cpsr_Q_IFM_thm = store_thm(
    "write_cpsr_Q_IFM_thm",
    ``preserve_relation_mmu (write_cpsr <|proc := 0|> (cpsr with <|Q := something; I := xI; F := xF; M := 16w|>)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)``,
    Q.ABBREV_TAC `cpsr2 = (cpsr with Q := something)`
      THEN `cpsr with <|Q := something; M := 16w; I := xI; F := xF|> = (cpsr2) with <|M := 16w; I := xI; F := xF|>` by Q.UNABBREV_TAC `cpsr2`
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN FULL_SIMP_TAC (srw_ss()) [write_cpsr_thm]);
add_to_simplist  write_cpsr_Q_IFM_thm;



val write_cpsr_J_T_IFM_thm = store_thm(
    "write_cpsr_J_T_IFM_thm",
    ``preserve_relation_mmu (write_cpsr <|proc := 0|> (cpsr with <|J := j; I := xI; F := xF;  T := t; M := 16w|>)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)``,
    Q.ABBREV_TAC `cpsr2 = (cpsr with <|J := j; T := t|>)`
      THEN `cpsr with <|J := j; T := t; M := 16w; I := xI; F := xF|> = (cpsr2) with <|M := 16w; I := xI; F := xF|>` by Q.UNABBREV_TAC `cpsr2`
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN FULL_SIMP_TAC (srw_ss()) [write_cpsr_thm]);
add_to_simplist  write_cpsr_J_T_IFM_thm;


val write_cpsr_flags_IFM_thm = store_thm(
    "write_cpsr_flags_IFM_thm",
    ``preserve_relation_mmu (write_cpsr <|proc := 0|> (cpsr with <|N := n; Z := z; C := c; V := v; I := xI; F := xF; M := 16w|>)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)``,
    Q.ABBREV_TAC `cpsr2 = (cpsr with <|N := n; Z := z; C := c; V := v|>)`
      THEN `cpsr with <|N := n; Z := z; C := c; V := v; M := 16w; I := xI; F := xF|> = (cpsr2) with <|M := 16w; I := xI; F := xF|>` by Q.UNABBREV_TAC `cpsr2`
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN FULL_SIMP_TAC (srw_ss()) [write_cpsr_thm]);
add_to_simplist  write_cpsr_flags_IFM_thm;


val write_cpsr_all_components_thm = store_thm(
    "write_cpsr_all_components_thm",
    ``preserve_relation_mmu (write_cpsr <|proc := 0|> (cpsr with <|N:=n; Z:=z; C:=c; V:=v; Q:=q; IT:=it; J:=j; GE:=ge; E:=e; T:=t; I := xI; F := xF; M := 16w|>)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)``,
    Q.ABBREV_TAC `cpsr2 = (cpsr with <|N:=n; Z:=z; C:=c; V:=v; Q:=q; IT:=it; J:=j; GE:=ge; E:=e; T:=t|>)`
      THEN `cpsr with <|N:=n; Z:=z; C:=c; V:=v; Q:=q; IT:=it; J:=j; GE:=ge; E:=e; T:=t; I := xI; F := xF; M := 16w|> = (cpsr2) with <|M := 16w; I := xI; F := xF|>` by Q.UNABBREV_TAC `cpsr2`
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN FULL_SIMP_TAC (srw_ss()) [write_cpsr_thm]);
add_to_simplist  write_cpsr_all_components_thm;



(**********************  simplifications  ***************************)
(**********************  4. applications  ***************************)



(* write e *)

g `!e. preserve_relation_mmu (write_e <|proc:=0|> e) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(STRIP_TAC);
e(ASSUME_TAC (SPECL [``(write_e <|proc := 0|> e):(unit M)``, ``(assert_mode 16w):(arm_state->bool)``, ``(assert_mode 16w):(arm_state->bool)``, ``empty_unt``, ``empty_sim``] (INST_TYPE [alpha |-> type_of(``()``)] fix_flags_lem)));
e(NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []));
e(PAT_ASSUM ``X``  FORCE_REV_REWRITE_TAC);
e(RW_TAC (srw_ss()) [write_e_def]);
e(ASSUME_TAC (SPECL [``(λcpsr. write_cpsr <|proc := 0|> (cpsr with E := e)):(ARMpsr -> unit M)``, ``(assert_mode 16w):(arm_state->bool)``,  ``empty_unt``, ``(empty_sim):(word32->arm_state->arm_state->bool)``, ``xI:bool``, ``xF:bool``] (INST_TYPE [alpha |-> type_of(``()``)] cpsr_simp_rel_ext_lem)));
e(FULL_SIMP_TAC (srw_ss()) []);
go_on 1;
val write_e_empty_thm = save_thm("write_e_empty_thm", top_thm());
val write_e_thm = save_thm("write_e_thm", MATCH_MP extras_lem2 (SPEC_ALL write_e_empty_thm));


(* write ge *)

g `!e. preserve_relation_mmu (write_ge <|proc:=0|> ge) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(STRIP_TAC);
e(ASSUME_TAC (SPECL [``(write_ge <|proc := 0|> ge):(unit M)``, ``(assert_mode 16w):(arm_state->bool)``, ``(assert_mode 16w):(arm_state->bool)``, ``empty_unt``, ``empty_sim``] (INST_TYPE [alpha |-> type_of(``()``)] fix_flags_lem)));
e(NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []));
e(PAT_ASSUM ``X``  FORCE_REV_REWRITE_TAC);
e(RW_TAC (srw_ss()) [write_ge_def]);
e(ASSUME_TAC (SPECL [``(λcpsr. write_cpsr <|proc := 0|> (cpsr with GE := ge)):(ARMpsr -> unit M)``, ``(assert_mode 16w):(arm_state->bool)``,  ``empty_unt``, ``(empty_sim):(word32->arm_state->arm_state->bool)``, ``xI:bool``, ``xF:bool``] (INST_TYPE [alpha |-> type_of(``()``)] cpsr_simp_rel_ext_lem)));
e(FULL_SIMP_TAC (srw_ss()) []);
go_on 1;
val write_ge_empty_thm = save_thm("write_ge_empty_thm", top_thm());
val write_ge_thm = save_thm("write_ge_thm", MATCH_MP extras_lem2 (SPEC_ALL write_ge_empty_thm));



(* write is et state*)


g `!e. preserve_relation_mmu (write_isetstate <|proc:=0|> isetstate) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(STRIP_TAC);
e(ASSUME_TAC (SPECL [``(write_isetstate <|proc := 0|> isetstate):(unit M)``, ``(assert_mode 16w):(arm_state->bool)``, ``(assert_mode 16w):(arm_state->bool)``, ``empty_unt``, ``empty_sim``] (INST_TYPE [alpha |-> type_of(``()``)] fix_flags_lem)));
e(NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []));
e(PAT_ASSUM ``X``  FORCE_REV_REWRITE_TAC);
e(RW_TAC (srw_ss()) [write_isetstate_def]);
e(ASSUME_TAC (SPECL [``(λcpsr. write_cpsr <|proc := 0|> (cpsr with <|J := (isetstate:word2) ' 1; T := isetstate ' 0 |>)):(ARMpsr -> unit M)``, ``(assert_mode 16w):(arm_state->bool)``,  ``empty_unt``, ``(empty_sim):(word32->arm_state->arm_state->bool)``, ``xI:bool``, ``xF:bool``] (INST_TYPE [alpha |-> type_of(``()``)] cpsr_simp_rel_ext_lem)));
e(FULL_SIMP_TAC (srw_ss()) []);
go_on 1;
val write_isetstate_empty_thm = save_thm("write_isetstate_empty_thm", top_thm());
val write_isetstate_thm = save_thm("write_isetstate_thm", MATCH_MP extras_lem2 (SPEC_ALL write_isetstate_empty_thm));



(* write flags *)

g `!e. preserve_relation_mmu (write_flags<|proc:=0|> (n,z,c,v)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(STRIP_TAC);
e(ASSUME_TAC (SPECL [``(write_flags <|proc := 0|> (n,z,c,v)):(unit M)``, ``(assert_mode 16w):(arm_state->bool)``, ``(assert_mode 16w):(arm_state->bool)``, ``empty_unt``, ``empty_sim``] (INST_TYPE [alpha |-> type_of(``()``)] fix_flags_lem)));
e(NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []));
e(PAT_ASSUM ``X``  FORCE_REV_REWRITE_TAC);
e(RW_TAC (srw_ss()) [write_flags_def]);
e(ASSUME_TAC (SPECL [``(λcpsr. write_cpsr <|proc := 0|> (cpsr with <|N := n; Z := z; C := c; V := v|>)):(ARMpsr -> unit M)``, ``(assert_mode 16w):(arm_state->bool)``,  ``empty_unt``, ``(empty_sim):(word32->arm_state->arm_state->bool)``, ``xI:bool``, ``xF:bool``] (INST_TYPE [alpha |-> type_of(``()``)] cpsr_simp_rel_ext_lem)));
e(FULL_SIMP_TAC (srw_ss()) []);
go_on 1;
val write_flags_empty_thm = save_thm("write_flags_empty_thm", top_thm());
val write_flags_thm = save_thm("write_flags_thm", MATCH_MP extras_lem2 (SPEC_ALL write_flags_empty_thm));




(* IT advance *)

g `preserve_relation_mmu (read_cpsr <|proc:=0|> >>=
           (λcpsr.
              if (cpsr.IT = 0w) ∨ cpsr.T then
                write_cpsr <|proc:=0|> (cpsr with IT := ITAdvance cpsr.IT)
              else
                errorT "IT_advance: unpredictable")) (assert_mode 16w) (assert_mode 16w) (empty_unt) (fix_flags xI xF empty_sim)`;
e(ASSUME_TAC (SPECL [``(λcpsr. if (cpsr.IT = 0w) ∨ cpsr.T then
                write_cpsr <|proc:=0|> (cpsr with IT := ITAdvance cpsr.IT)
              else
                errorT "IT_advance: unpredictable"):(ARMpsr -> unit M)``, ``(assert_mode 16w):(arm_state->bool)``,  ``empty_unt``, ``(empty_sim):(word32->arm_state->arm_state->bool)``, ``xI:bool``, ``xF:bool``] (INST_TYPE [alpha |-> type_of(``()``)] cpsr_simp_rel_ext_lem)));
e(FULL_SIMP_TAC (srw_ss()) []);
go_on 1;
val it_advance_help_thm = MATCH_MP ((CONJUNCT2 (SPEC_ALL fix_flags_lem))) (GEN_ALL (top_thm()));
add_to_simplist it_advance_help_thm;
val IT_advance_empty_thm = prove_and_save(``IT_advance <|proc:=0|>``, "IT_advance_empty_thm");
val IT_advance_thm = save_thm("IT_advance_thm", MATCH_MP extras_lem2 (SPEC_ALL IT_advance_empty_thm));




(* set q  *)

g `!e. preserve_relation_mmu (set_q <|proc:=0|>) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(STRIP_TAC);
e(ASSUME_TAC (SPECL [``(set_q <|proc := 0|> ):(unit M)``, ``(assert_mode 16w):(arm_state->bool)``, ``(assert_mode 16w):(arm_state->bool)``, ``empty_unt``, ``empty_sim``] (INST_TYPE [alpha |-> type_of(``()``)] fix_flags_lem)));
e(NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []));
e(PAT_ASSUM ``X``  FORCE_REV_REWRITE_TAC);
e(RW_TAC (srw_ss()) [set_q_def]);
e(ASSUME_TAC (SPECL [``(λcpsr. write_cpsr <|proc := 0|> (cpsr with Q := T)):(ARMpsr -> unit M)``, ``(assert_mode 16w):(arm_state->bool)``,  ``empty_unt``, ``(empty_sim):(word32->arm_state->arm_state->bool)``, ``xI:bool``, ``xF:bool``] (INST_TYPE [alpha |-> type_of(``()``)] cpsr_simp_rel_ext_lem)));
e(FULL_SIMP_TAC (srw_ss()) []);
go_on 1;
val set_q_empty_thm = save_thm("set_q_empty_thm", top_thm());
val set_q_thm = save_thm("set_q_thm", MATCH_MP extras_lem2 (SPEC_ALL set_q_empty_thm));




(* read spsr *)


g `preserve_relation_mmu (read_spsr <|proc:=0|>) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(ASSUME_TAC (SPECL [``(read_spsr <|proc := 0|> ):(ARMpsr M)``, ``(assert_mode 16w):(arm_state->bool)``, ``(assert_mode 16w):(arm_state->bool)``, ``empty_unt``, ``empty_sim``] (INST_TYPE [alpha |-> Type `:ARMpsr`] fix_flags_lem)));
e(NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []));
e(PAT_ASSUM ``X``  FORCE_REV_REWRITE_TAC);
e(RW_TAC (srw_ss()) [read_spsr_def]);
e(ASSUME_TAC (SPECL [``(λcpsr.
      bad_mode <|proc := 0|> cpsr.M >>=
      (λbad_mode.
         if bad_mode then
           errorT "read_spsr: unpredictable"
         else
           case cpsr.M of
              17w -> read__psr <|proc := 0|> SPSR_fiq
           || 18w -> read__psr <|proc := 0|> SPSR_irq
           || 19w -> read__psr <|proc := 0|> SPSR_svc
           || 22w -> read__psr <|proc := 0|> SPSR_mon
           || 23w -> read__psr <|proc := 0|> SPSR_abt
           || 27w -> read__psr <|proc := 0|> SPSR_und
           || cpsr.M -> errorT "read_spsr: unpredictable")):(ARMpsr -> ARMpsr M)``, ``(assert_mode 16w):(arm_state->bool)``,  ``empty_unt``, ``(empty_sim):(word32->arm_state->arm_state->bool)``, ``xI:bool``, ``xF:bool``] (INST_TYPE [alpha |-> Type `:ARMpsr`] cpsr_simp_rel_ext_lem)));
e(FULL_SIMP_TAC (srw_ss()) []);
go_on 1;
val read_spsr_empty_thm = save_thm("read_spsr_empty_thm", top_thm());
val read_spsr_thm = save_thm("read_spsr_thm", MATCH_MP extras_lem2 (SPEC_ALL read_spsr_empty_thm));


(* if-then *)
g ` preserve_relation_mmu
(read_cpsr <|proc :=0|> >>=
       (\cpsr.
          (increment_pc <|proc :=0|> Encoding_Thumb |||
           write_cpsr <|proc :=0|> (cpsr with IT := (something))) >>= (λ(u1,u2). return ()))) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim `;
e(ASSUME_TAC (SPECL [``(read_cpsr <|proc :=0|> >>=
       (\cpsr.
          (increment_pc <|proc :=0|> Encoding_Thumb |||
           write_cpsr <|proc :=0|> (cpsr with IT := (something))) >>= (λ(u1,u2). return ()))):(unit M)``, ``(assert_mode 16w: arm_state -> bool)``,  ``(assert_mode 16w: arm_state -> bool)``, ``empty_unt``, ``empty_sim``](INST_TYPE [alpha |-> type_of (``()``)] fix_flags_lem)));
e(NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []));
e(PAT_ASSUM ``X``  FORCE_REV_REWRITE_TAC);
e(RW_TAC (srw_ss()) []);
e(ASSUME_TAC (SPECL [``(\cpsr. (increment_pc <|proc := 0|> Encoding_Thumb
         ||| write_cpsr <|proc := 0|> (cpsr with IT := something)) >>=
      (λ(u1,u2). return ())):(ARMpsr -> unit M)``, ``(assert_mode 16w: arm_state -> bool)``, ``empty_unt``, ``(empty_sim):(word32->arm_state->arm_state->bool)``, ``xI:bool``, ``xF:bool``](INST_TYPE [alpha |-> type_of (``()``)] cpsr_simp_rel_ext_lem)));
e (FULL_SIMP_TAC (srw_ss()) [parT_def]);
go_on 1;
val if_then_instr_help_lem1 = MATCH_MP extras_lem2 (top_thm());


val if_then_instr_help_lem2 = store_thm(
    "if_then_instr_hel_lem2",
    `` preserve_relation_mmu (read_cpsr <|proc :=0|> >>=
       (\cpsr.
          (increment_pc <|proc :=0|> Encoding_Thumb |||
           write_cpsr <|proc :=0|> (cpsr with IT := (firstcond @@ mask))) >>= (λ(u1,u2). return ()))) (assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints priv_mode_similar``,
    ASSUME_TAC (SPECL [``xI:bool``, ``xF:bool``, ``(firstcond @@ mask):word8``] (GEN_ALL if_then_instr_help_lem1))
       THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_comb_16_27_thm]);
add_to_simplist if_then_instr_help_lem2;



val if_then_instr_comb_thm = prove_and_save_p (``if_then_instr <|proc:=0|> (If_Then firstcond mask)``, "if_then_instr_comb_thm", ``if_then_instr``);



(* check array *)



g` preserve_relation_mmu ((read_reg <|proc:=0|> 15w ||| read_reg <|proc:=0|> n ||| read_reg <|proc:=0|> m |||
        read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>=
         (\(pc,rn,rm,cpsr,teehbr).
          if rn <=+ rm then
            ((write_reg <|proc:=0|> 14w ((0 :+ T) pc) |||
              write_cpsr <|proc:=0|> (cpsr with IT := 0w)) >>=
             ( \ (u1:unit,u2:unit).
               branch_write_pc <|proc:=0|> (teehbr + 0xFFFFFFF8w)))
          else
            increment_pc <|proc:=0|> Encoding_ThumbEE))(assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)`;
e(ASSUME_TAC (SPECL [``15w:word4``, ``n:word4``, ``m:word4``, ``(\(pc,rn,rm,cpsr,teehbr).
          if rn <=+ rm then
            ((write_reg <|proc:=0|> 14w ((0 :+ T) pc) |||
              write_cpsr <|proc:=0|> (cpsr with IT := 0w)) >>=
             ( \ (u1:unit,u2:unit).
               branch_write_pc <|proc:=0|> (teehbr + 0xFFFFFFF8w)))
          else
            increment_pc <|proc:=0|> Encoding_ThumbEE):(word32 # word32 # word32 # ARMpsr # word32 -> unit M)``, ``(assert_mode 16w: arm_state -> bool)`` ](INST_TYPE [alpha |-> type_of (``()``)] cpsr_quintuple_simp_rel_ext_lem)));
e (FULL_SIMP_TAC (srw_ss()) [parT_def]);
go_on 1;
val check_array_instr_help_lem1 = (MATCH_MP extras_lem2 (MATCH_MP ((CONJUNCT2 (SPEC_ALL fix_flags_lem))) (GENL [``xI:bool``, ``xF:bool``] (top_thm()))));


val check_array_instr_help_lem2 = store_thm(
    "check_array_instr_help_lem2",
    `` preserve_relation_mmu ((read_reg <|proc:=0|> 15w ||| read_reg <|proc:=0|> n ||| read_reg <|proc:=0|> m |||
        read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>=
         (\(pc,rn,rm,cpsr,teehbr).
          if rn <=+ rm then
            ((write_reg <|proc:=0|> 14w ((0 :+ T) pc) |||
              write_cpsr <|proc:=0|> (cpsr with IT := 0w)) >>=
             ( \ (u1:unit,u2:unit).
               branch_write_pc <|proc:=0|> (teehbr + 0xFFFFFFF8w)))
          else
            increment_pc <|proc:=0|> Encoding_ThumbEE))(assert_mode 16w) (comb_mode 16w 27w) priv_mode_constraints priv_mode_similar``,
    ASSUME_TAC check_array_instr_help_lem1
       THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_comb_16_27_thm]);
add_to_simplist check_array_instr_help_lem2;

val check_array_instr_comb_thm = prove_and_save_p (``check_array_instr <|proc:=0|> (Check_Array n m)``, "check_array_instr_comb_thm", ``check_array_instr``);


(* null check if thumbee *)

g `preserve_relation_mmu((read_reg <|proc:=0|> 15w ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>=
            (\(pc,cpsr,teehbr).
               (write_reg <|proc:=0|> 14w ((0 :+ T) pc) |||
                write_cpsr <|proc:=0|> (cpsr with IT := 0w)) >>=
               (\(u1:unit, u2:unit).
                 branch_write_pc <|proc:=0|> (teehbr  + 0xFFFFFFFCw))))(assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)`;
e(ASSUME_TAC (SPECL [`` (\(pc,cpsr,teehbr).
               (write_reg <|proc:=0|> 14w ((0 :+ T) pc) |||
                write_cpsr <|proc:=0|> (cpsr with IT := 0w)) >>=
               (\(u1:unit, u2:unit).
                 branch_write_pc <|proc:=0|> (teehbr  + 0xFFFFFFFCw))):(word32 # ARMpsr # word32 -> unit M)``, ``(assert_mode 16w: arm_state -> bool)``] (INST_TYPE [alpha |-> type_of (``()``)] cpsr_triple_simp_rel_ext_lem)));
e (FULL_SIMP_TAC (srw_ss()) [parT_def]);
go_on 1;
val null_check_if_thumbee_help_lem = (MATCH_MP extras_lem2 (MATCH_MP ((CONJUNCT2 (SPEC_ALL fix_flags_lem))) (GENL [``xI:bool``, ``xF:bool``] (top_thm()))));
add_to_simplist null_check_if_thumbee_help_lem;







