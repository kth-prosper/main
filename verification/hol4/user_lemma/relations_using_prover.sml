(* ========= read_reg ============*)


g `preserve_relation_mmu (LookUpRName <|proc:=0|> (t,M)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
go_on 1;
val LookUpRName_thm =  save_thm("LookUpRName_thm", top_thm());


g `(~ access_violation s) ==> (((LookUpRName <|proc := 0|> (nw,16w)) s) = ValueState reg s') ==> (reg IN  {RName_0usr; RName_1usr; RName_2usr; RName_3usr; RName_4usr; RName_5usr; RName_6usr; RName_7usr; RName_8usr; RName_9usr; RName_10usr; RName_11usr; RName_12usr; RName_SPusr; RName_LRusr; RName_PC})`;
e(EVAL_TAC);
e(RW_TAC (srw_ss()) [] THEN METIS_TAC []);
val lookup_read__reg_help_lem1 = top_thm();


g `(nw <> 15w) ==> (access_violation s) ==> ((((LookUpRName <|proc := 0|> (nw,16w)  >>=  (λrname. read__reg <|proc := 0|> rname)) s) = ValueState ARB s)) `;
e(EVAL_TAC);
e(RW_TAC (srw_ss())  []);
e(IMP_RES_TAC (blastLib.BBLAST_PROVE ``((nw:word4) <> (0w:word4)) ==> (nw <> 1w) ==> (nw <> 2w) ==> (nw <> 3w) ==> (nw <> 4w)  ==> (nw <> 5w) ==> (nw <> 6w) ==> (nw <> 7w) ==> (nw <> 8w) ==> (nw <> 9w) ==> (nw <> 10w) ==> (nw <> 11w) ==> (nw <> 12w)  ==> (nw <> 13w) ==> (nw <> 14w) ==> (nw = 15w)``)); 
val lookup_read__reg_help_lem2 = top_thm();


g `(nw = 15w) ==> (access_violation s) ==>  (((LookUpRName <|proc := 0|> (nw,16w)  >>=  (λrname. read__reg <|proc := 0|> rname)) s) = Error "LookUpRName: n = 15w") `;
e(EVAL_TAC);
e(RW_TAC (srw_ss())  []); 
val lookup_read__reg_help_lem3 = top_thm();


g ` preserve_relation_mmu (LookUpRName <|proc := 0|> (nw,16w) >>=  (λrname. read__reg <|proc := 0|> rname)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(RW_TAC (srw_ss()) [preserve_relation_mmu_def, empty_unt_def, empty_sim_def]);
e(`access_violation s1 = access_violation s2` by METIS_TAC [similar_def]);
e(Cases_on `access_violation s1`);
(* access violation from beginning *)
e(`access_violation s2` by FULL_SIMP_TAC (srw_ss()) []);
e(Cases_on `nw = 15w`);
(* nw = 15 *)
e(IMP_RES_TAC lookup_read__reg_help_lem3);
e(RW_TAC (srw_ss()) []);
(* nw <> 15 *)
e(IMP_RES_TAC lookup_read__reg_help_lem2);
e(RW_TAC (srw_ss()) [untouched_refl]);
(* no access violation from beginning *)
e(`~ access_violation s2` by FULL_SIMP_TAC (srw_ss()) []);
e(ASSUME_TAC (SPECL [``nw:word4``,``16w:word5``] (GEN_ALL LookUpRName_thm)));
e(FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def, empty_sim_def, empty_unt_def]);
e(SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``]));
e(UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []);
(* received same value in Lookup *)
e(`access_violation s1' = access_violation s2'` by METIS_TAC [similar_def]);
e(FULL_SIMP_TAC (srw_ss()) [seqT_def, read__reg_def, constT_def, readT_def]);
e(RW_TAC (srw_ss()) []);
e(ASSUME_TAC  (SPECL [``s1':arm_state``, ``s1:arm_state``, ``a:RName``, ``nw:word4``] (GEN_ALL lookup_read__reg_help_lem1)));
e(FULL_SIMP_TAC (srw_ss()) [similar_def, equal_user_register_def]);
e(SPEC_ASSUM_TAC (``!(reg:RName). X``, [``a:RName``]));
e(UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []);
(* Error in Lookup *)
e(RW_TAC (srw_ss()) [seqT_def]);
val lookup_read__reg_thm = top_thm();
add_to_simplist lookup_read__reg_thm;


g `preserve_relation_mmu (read_reg_mode <|proc:=0|> (nw, 16w)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
go_on 1;
val read_reg_mode_thm =  save_thm ("read_reg_mode_thm", (MATCH_MP extras_lem2 (top_thm())));


g `preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (λcpsr. read_reg_mode <|proc:=0|> (n,16w))) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
go_on 1;
val read_cpsr_read_reg_mode_16_thm = save_thm("read_cpsr_read_reg_mode_16_thm", top_thm());


g `preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (λcpsr. read_reg_mode <|proc:=0|> (n,cpsr.M))) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(ASSUME_TAC (SPECL [``(\c. read_reg_mode <|proc:=0|> (n, c.M))``, ``assert_mode 16w``] (INST_TYPE [alpha |-> Type `:word32`] cpsr_simp_rel_lem)));
e(ASSUME_TAC read_cpsr_read_reg_mode_16_thm);
e(FULL_SIMP_TAC (srw_ss()) []);
val read_cpsr_read_reg_mode_thm = top_thm();
add_to_simplist read_cpsr_read_reg_mode_thm;


val (read_reg_empty_thm, _) =  prove_it ``read_reg <|proc:=0|> n`` ``assert_mode 16w`` ``assert_mode 16w`` ``empty_unt`` ``empty_sim``;
val read_reg_thm = save_thm("read_reg_thm", MATCH_MP extras_lem2 read_reg_empty_thm);



(* ========= write_reg ============*)


g `(nw <> 15w) ==> (access_violation s) ==> ((((LookUpRName <|proc := 0|> (nw,16w)  >>=  ( \ rname. write__reg <|proc := 0|> rname value)) s) = (ValueState () s))) `;
e(EVAL_TAC);
e(RW_TAC (srw_ss())  [] 
   THEN `!(x:unit). x = ()` by (Cases_on `x` THEN EVAL_TAC)
   THEN SPEC_ASSUM_TAC (``!x. X``, [``ARB:unit``])
   THEN FULL_SIMP_TAC (srw_ss()) []);
e(IMP_RES_TAC (blastLib.BBLAST_PROVE ``((nw:word4) <> (0w:word4)) ==> (nw <> 1w) ==> (nw <> 2w) ==> (nw <> 3w) ==> (nw <> 4w)  ==> (nw <> 5w) ==> (nw <> 6w) ==> (nw <> 7w) ==> (nw <> 8w) ==> (nw <> 9w) ==> (nw <> 10w) ==> (nw <> 11w) ==> (nw <> 12w)  ==> (nw <> 13w) ==> (nw <> 14w) ==> (nw = 15w)``)); 
val lookup_write__reg_help_lem2 = top_thm();


g `(nw = 15w) ==> (access_violation s) ==>  (((LookUpRName <|proc := 0|> (nw,16w)  >>=  (λrname. write__reg <|proc := 0|> rname value)) s) = Error "LookUpRName: n = 15w") `;
e(EVAL_TAC);
e(RW_TAC (srw_ss())  []); 
val lookup_write__reg_help_lem3 = top_thm();


g ` preserve_relation_mmu (LookUpRName <|proc := 0|> (nw,16w) >>=  (λrname. write__reg <|proc := 0|> rname value)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(RW_TAC (srw_ss()) [preserve_relation_mmu_def, empty_unt_def, empty_sim_def]);
e(`access_violation s1 = access_violation s2` by METIS_TAC [similar_def]);
e(Cases_on `access_violation s1`);
(* access violation from beginning *)
e(`access_violation s2` by FULL_SIMP_TAC (srw_ss()) []);
e(Cases_on `nw = 15w`);
(* nw = 15 *)
e(IMP_RES_TAC lookup_write__reg_help_lem3);
e(RW_TAC (srw_ss()) []);
(* nw <> 15 *)
e(IMP_RES_TAC lookup_write__reg_help_lem2);
e(RW_TAC (srw_ss()) [untouched_refl]);
(* no access violation from beginning *)
e(`~ access_violation s2` by FULL_SIMP_TAC (srw_ss()) []);
e(ASSUME_TAC (SPECL [``nw:word4``,``16w:word5``] (GEN_ALL LookUpRName_thm)));
e(FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def, empty_sim_def, empty_unt_def]);
e(SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``]));
e(UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []);
(* received same value in Lookup *)
e(DISJ1_TAC);
e(`access_violation s1' = access_violation s2'` by METIS_TAC [similar_def]);
e(Cases_on `access_violation s2'` THEN FULL_SIMP_TAC (srw_ss()) [seqT_def, write__reg_def, constT_def, writeT_def]);
e(RW_TAC (srw_ss()) []);
(*** untouched 1 *) 
e(IMP_RES_TAC  (SPECL [``s1':arm_state``, ``s1:arm_state``, ``a:RName``, ``nw:word4``] (GEN_ALL lookup_read__reg_help_lem1))
               THEN FULL_SIMP_TAC (srw_ss()) [assert_mode_def, untouched_def, LET_DEF]
               THEN RW_TAC (srw_ss()) []
               THEN REPEAT (UNDISCH_MATCH_TAC ``(reg:RName) <> rn_u``)
               THEN EVAL_TAC
               THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []);
(*** untouched 2 *)
e (IMP_RES_TAC  (SPECL [``s2':arm_state``, ``s2:arm_state``, ``a:RName``, ``nw:word4``] (GEN_ALL lookup_read__reg_help_lem1))   
               THEN FULL_SIMP_TAC (srw_ss()) [assert_mode_def, untouched_def, LET_DEF]
               THEN RW_TAC (srw_ss()) []
               THEN REPEAT (UNDISCH_MATCH_TAC ``(reg:RName) <> rn_u``)
               THEN EVAL_TAC
               THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []);
(*** mode 1 *)               
e(FULL_SIMP_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def]);
(*** mode w *)               
e(FULL_SIMP_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, ARM_READ_CPSR_def]);
(*** similar *)
e(UNDISCH_TAC ``similar g s1' s2'``);
e(EVAL_TAC);
e((REPEAT (STRIP_TAC)) THEN FULL_SIMP_TAC (srw_ss()) []);
e(IMP_RES_TAC untouched_mmu_setup_lem);
e(ASSUME_TAC (SPECL [``s1':arm_state``, ``s1' with registers updated_by ((0,a) =+ value)``, ``g:word32``] trivially_untouched_av_lem));
e(ASSUME_TAC (SPECL [``s2':arm_state``, ``s2' with registers updated_by ((0,a) =+ value)``, ``g:word32``] trivially_untouched_av_lem));
e(FULL_SIMP_TAC (srw_ss()) []);
(* Error in Lookup *)
e(RW_TAC (srw_ss()) [seqT_def]);
val lookup_write__reg_thm = top_thm();
add_to_simplist lookup_write__reg_thm;


g `preserve_relation_mmu (write_reg_mode <|proc:=0|> (nw, 16w) value) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
go_on 1;
val write_reg_mode_thm =  save_thm ("write_reg_mode_thm", (MATCH_MP extras_lem2 (top_thm())));


g `preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (λcpsr. write_reg_mode <|proc:=0|> (n,16w) value)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
go_on 1;
val read_cpsr_read_reg_mode_16_thm = save_thm("read_cpsr_write_reg_mode_16_thm", top_thm());


g `preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (λcpsr. write_reg_mode <|proc:=0|> (n,cpsr.M) value)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(ASSUME_TAC (SPECL [``(\c. write_reg_mode <|proc:=0|> (n, c.M) value)``, ``assert_mode 16w``] (INST_TYPE [alpha |-> Type `:unit`] cpsr_simp_rel_lem)));
e(ASSUME_TAC read_cpsr_read_reg_mode_16_thm);
e(FULL_SIMP_TAC (srw_ss()) []);
val read_cpsr_write_reg_mode_thm = top_thm();
add_to_simplist read_cpsr_write_reg_mode_thm;


val (write_reg_empty_thm, _) =  prove_it ``write_reg <|proc:=0|> n value`` ``assert_mode 16w`` ``assert_mode 16w`` ``empty_unt`` ``empty_sim``;
val write_reg_thm = save_thm("write_reg_thm", MATCH_MP extras_lem2 write_reg_empty_thm);


 
(* ===================================================================== *)


(* arch version *)

val arch_version_alternative_def = store_thm(
    "arch_version_alternative_def",
    ``arch_version ii = (read_arch ii >>= (\arch. constT(version_number arch)))``,
    RW_TAC (srw_ss()) [arch_version_def, constT_def, seqT_def]);

g `preserve_relation_mmu (arch_version <|proc:=0|>) 
	      (assert_mode 16w) (assert_mode  16w) strict_unt empty_sim`;
e(RW_TAC (srw_ss()) [arch_version_alternative_def]);
go_on 1;
val arch_version_thm = save_thm("arch_version_thm", (MATCH_MP extras_lem4 (SPEC_ALL (top_thm()))));

 
(* ===================================================================== *)



(* address mode *)



g `preserve_relation_mmu (thumb_expand_imm_c (imm12,c_in)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(RW_TAC (srw_ss()) [thumb_expand_imm_c_def, LET_DEF]);
e(Cases_on `(9 >< 8) (imm12:word12) = (0w:word2)` THEN Cases_on `(9 >< 8) imm12 = (1w:word2)` THEN Cases_on `(9 >< 8) imm12 = (2w:word2)` THEN Cases_on `(9 >< 8) imm12 = (3w:word2)`  THEN FULL_SIMP_TAC (srw_ss()) []);
go_on 4;
e(ASSUME_TAC (blastLib.BBLAST_PROVE ``((((9 >< 8) (imm12:word12)) <> (0w:word2)) /\ (((9 >< 8) imm12) <> (1w:word2)) /\ (((9 >< 8) imm12) <> (2w:word2)) /\ (((9 >< 8) imm12) <> (3w:word2))) ==> F``));
e(UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []);
e(Cases_on `(9 >< 8) (imm12:word12) = (0w:word2)` THEN Cases_on `(9 >< 8) imm12 = (1w:word2)` THEN Cases_on `(9 >< 8) imm12 = (2w:word2)` THEN Cases_on `(9 >< 8) imm12 = (3w:word2)`  THEN FULL_SIMP_TAC (srw_ss()) []);
go_on 4;
e(ASSUME_TAC (blastLib.BBLAST_PROVE ``((((9 >< 8) (imm12:word12)) <> (0w:word2)) /\ (((9 >< 8) imm12) <> (1w:word2)) /\ (((9 >< 8) imm12) <> (2w:word2)) /\ (((9 >< 8) imm12) <> (3w:word2))) ==> F``));
e(UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []);
go_on 1;
val thumb_expand_imm_c_thm = save_thm("thumb_expand_imm_c_thm", (MATCH_MP extras_lem2 (SPEC_ALL (top_thm()))));



g `preserve_relation_mmu (address_mode1 <|proc:=0|> enc mode1) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(Cases_on `mode1` THEN RW_TAC (srw_ss()) [address_mode1_def, LET_DEF]);
go_on 1;
e(PairedLambda.GEN_BETA_TAC);
go_on 1;
go_on 1;
val address_mode1_thm = save_thm("address_mode1_thm", (MATCH_MP extras_lem2 (SPEC_ALL (top_thm()))));


g `preserve_relation_mmu (address_mode2 <|proc:=0|> indx add rn mode2) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(Cases_on `mode2` THEN RW_TAC (srw_ss()) [address_mode2_def, LET_DEF]);
go_on 4;
e(PairedLambda.GEN_BETA_TAC);
go_on 1;
val address_mode2_thm = save_thm("address_mode2_thm", (MATCH_MP extras_lem2 (SPEC_ALL (top_thm()))));


g `preserve_relation_mmu (address_mode3 <|proc:=0|> indx add rn mode3) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(Cases_on `mode3` THEN RW_TAC (srw_ss()) [address_mode3_def, LET_DEF]);
go_on 4;
e(PairedLambda.GEN_BETA_TAC);
go_on 1;
val address_mode3_thm = save_thm("address_mode3_thm", (MATCH_MP extras_lem2 (SPEC_ALL (top_thm()))));



(* ===================================================================== *)


val read_memA_with_priv_thm = prove_and_save_s (``read_memA_with_priv <|proc:=0|> (add, n, p)``, "read_memA_with_priv_thm");


val read_memA_with_priv_loop_body_thm = prove_and_save (``λi. read_memA_with_priv <|proc:=0|> (address + n2w i,1,privileged)``, "read_memA_with_priv_loop_body_thm");

val read_memA_with_priv_loop_thm = store_thm(
    "read_memA_with_priv_loop_thm",
    ``preserve_relation_mmu (forT 0 (size − 1)
             (λi.
                read_memA_with_priv <|proc:=0|>
                  (address + n2w i,1,privileged))) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim``,
   ASSUME_TAC read_memA_with_priv_loop_body_thm
      THEN FULL_SIMP_TAC (srw_ss()) [trans_empty_unt_thm, reflex_empty_unt_thm, reflex_empty_sim_thm, forT_preserving_thm]);
add_to_simplist read_memA_with_priv_loop_thm;

g `preserve_relation_mmu (read_memU_with_priv <|proc:=0|> (address:word32, size:num, privileged:bool)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(FULL_SIMP_TAC (srw_ss()) [read_memU_with_priv_def, LET_DEF]);
go_on 1;
val read_memU_with_priv_thm = save_thm ("read_memU_with_priv_thm", (MATCH_MP extras_lem2 (SPEC_ALL (top_thm()))));


val write_memA_with_priv_empty_thm = prove_and_save (``write_memA_with_priv <|proc:=0|> (add, size, p) vl``, "write_memA_with_priv_empty_thm");
val write_memA_with_priv_thm = save_thm("write_memA_wih_priv_thm", (MATCH_MP extras_lem2 (SPEC_ALL write_memA_with_priv_empty_thm)));

val write_memA_with_priv_loop_body_thm = prove_and_save (``λi. write_memA_with_priv <|proc:=0|> (address + n2w i,1,privileged) [EL i value]``, "write_memA_with_priv_loop_body_thm");

val write_memA_with_priv_loop_thm = store_thm(
    "write_memA_with_priv_loop_thm",
    ``preserve_relation_mmu (forT 0 (size − 1) (λi. write_memA_with_priv <|proc:=0|> (address + n2w i,1,privileged) [EL i value])) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim``,
   ASSUME_TAC write_memA_with_priv_loop_body_thm
      THEN FULL_SIMP_TAC (srw_ss()) [trans_empty_unt_thm, reflex_empty_unt_thm, reflex_empty_sim_thm, forT_preserving_thm]);
add_to_simplist write_memA_with_priv_loop_thm;

val write_memU_with_priv_empty_thm = prove_and_save (``write_memU_with_priv <|proc:=0|> (address:word32, size:num, privileged:bool) x``, "write_memU_with_priv_empty_thm");
val write_memU_with_priv_thm = save_thm ("write_memU_with_priv_thm", (MATCH_MP extras_lem2 (SPEC_ALL (write_memU_with_priv_empty_thm))));


g `preserve_relation_mmu (set_exclusive_monitors <|proc:=0|> (add, n)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(FULL_SIMP_TAC (srw_ss()) [set_exclusive_monitors_def, LET_DEF]);
go_on 1;
val set_exclusive_monitors_thm = save_thm("set_exclusive_monitors_thm", (MATCH_MP extras_lem2 (SPEC_ALL (top_thm()))));


g `preserve_relation_mmu
  ((λ(passed,state').
      write_monitor <|proc := 0|> (monitor with state := state') >>=
      (λu. return passed))
     ((λ(local_passed,x').
         (λ(passed,x).
            (if passed then
               (λy. (λ(u,x). (T,x)) (monitor.ClearExclusiveLocal 0 y))
             else
               (λy. (F,y))) x)
           ((if memaddrdesc.memattrs.shareable then
               (λy.
                  (λ(global_passed,x). (local_passed ∧ global_passed,x))
                    (monitor.IsExclusiveGlobal
                       (memaddrdesc.paddress,<|proc := 0|>,n) y))
             else
               (λy. (local_passed,y))) x'))
        (monitor.IsExclusiveLocal (memaddrdesc.paddress,<|proc := 0|>,n)
           monitor.state))) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim `;
e(Cases_on `(monitor.IsExclusiveLocal (memaddrdesc.paddress,<|proc := 0|>,n)
           monitor.state)`
   THEN RW_TAC (srw_ss()) [] 
   THEN Cases_on `(monitor.IsExclusiveGlobal
              (memaddrdesc.paddress,<|proc := 0|>,n) r)`
   THEN RW_TAC (srw_ss()) []
   THEN Cases_on ` (monitor.ClearExclusiveLocal 0 r')`
   THEN Cases_on ` (monitor.ClearExclusiveLocal 0 r)`
   THEN RW_TAC (srw_ss()) []);
go_on 4;
val exclusive_monitors_pass_help_thm = save_thm("exclusive_monitors_pass_help_thm", top_thm());
add_to_simplist exclusive_monitors_pass_help_thm;


g `preserve_relation_mmu (exclusive_monitors_pass <|proc:=0|> (add,n)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(FULL_SIMP_TAC (srw_ss()) [exclusive_monitors_pass_def, seqE_def, constE_def, LET_DEF]);
go_on 1;
val exclusive_monitors_pass_thm = save_thm("exclusive_monitors_pass_thm", (MATCH_MP extras_lem2 (SPEC_ALL (top_thm()))));

