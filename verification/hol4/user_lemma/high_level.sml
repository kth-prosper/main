;

val you_and_me_thm = Q.prove(`guest1 <> guest2`, RW_TAC (srw_ss()) [guest1_def, guest2_def, global_vm_0_add_axiom, global_vm_1_add_axiom]);




(***************  get SIMILAR  *******************)

val cus_to_similar_thm = store_thm(
    "cus_to_similar_thm",
    `` ((correct_user_mode_states sr si guest1) ==> (similar guest1 sr si.machine1))
    /\ ((correct_user_mode_states sr si guest2) ==> (similar guest2 sr si.machine2))``,
    STRIP_TAC
      THEN ASSUME_TAC you_and_me_thm
      THEN (RW_TAC (srw_ss()) [similar_def, LET_DEF]
      THENL [(* mem *)
             FULL_SIMP_TAC (srw_ss()) [guests_equal_memory_def, correct_user_mode_states_def, LET_DEF],
             (* psrs *)
             FULL_SIMP_TAC (srw_ss()) [active_guest_equal_regs_psrs_def, you_and_me_thm, correct_user_mode_states_def, LET_DEF],
             (* equal_user_register *)
             FULL_SIMP_TAC (srw_ss()) [ correct_user_mode_states_def, LET_DEF, active_guest_equal_regs_psrs_def, user_regs_from_state_def, equal_user_register_def, LET_DEF, LookUp_UserRName_def, read__reg_def, readT_def, user_regs_from_list_def, you_and_me_thm]
               THEN PAT_ASSUM ``RName_User_case x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 = RName_User_case y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16`` (fn th =>  (ASSUME_TAC (LIST_CONJ( map ( fn rname => (MK_COMB (th, Q.prove (`^rname = ^rname`, RW_TAC (arith_ss) [])))) [``RName_0usr``,  ``RName_1usr``,  ``RName_2usr``,  ``RName_3usr``,  ``RName_4usr``,  ``RName_5usr``,  ``RName_6usr``,  ``RName_7usr``,  ``RName_8usr``,  ``RName_9usr``,  ``RName_10usr``,   ``RName_11usr``,  ``RName_12usr``,  ``RName_SPusr``,  ``RName_LRusr``,  ``RName_PC``])) THEN FULL_SIMP_TAC (srw_ss()) []))
               THEN RW_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (srw_ss()) [],
             (* coprocessors *)
             FULL_SIMP_TAC (srw_ss()) [LET_DEF, coprocessor_constrains_def, correct_user_mode_states_def]
                THEN Cases_on `sr.coprocessors.state` 
                THEN Cases_on `si.machine1.coprocessors.state` 
                THEN Cases_on `si.machine2.coprocessors.state`
                THEN Cases_on `C0`
                THEN Cases_on `C0'` 
                THEN Cases_on `C0''`
                THEN FULL_SIMP_TAC (srw_ss()) [],
             (* interrupt wait etc. *)
             FULL_SIMP_TAC (srw_ss()) [LET_DEF, user_mode_constraints_def, correct_user_mode_states_def],
             (* access violation *)
             FULL_SIMP_TAC (srw_ss()) [LET_DEF, user_mode_constraints_def, correct_user_mode_states_def, you_and_me_thm],
             (* info *)
             FULL_SIMP_TAC (srw_ss()) [LET_DEF, user_mode_constraints_def, correct_user_mode_states_def],
             (* monitors *)
             FULL_SIMP_TAC (srw_ss()) [LET_DEF, user_mode_constraints_def, correct_user_mode_states_def],
             (* event registers *)
             FULL_SIMP_TAC (srw_ss()) [LET_DEF, user_mode_constraints_def, correct_user_mode_states_def]]));


(***************  effects of instruction execution  *******************)

val constant_other_parts_on_machine_update_lem = store_thm(
    "constant_other_parts_on_machine_update_lem",
    ``   ((s with machine1 := b).logical_component = s.logical_component)
      /\ ((s with machine2 := b).logical_component = s.logical_component)
      /\ ((s with machine1 := b).machine2          = s.machine2)
      /\ ((s with machine2 := b).machine1          = s.machine1)``,
    EVAL_TAC);


val constant_logical_component_lem = store_thm(
    "constant_logical_component_lem",
    `` (one_step_ideal si cycle <|proc:=0|> = (ValueState tb inext,rc,mode')) ==> (si.logical_component = inext.logical_component)``,
    FULL_SIMP_TAC (srw_ss()) [one_step_ideal_def,  LET_DEF, constTC_def, execute_instr_ideal_def, update_machine_def, errorTC_def]
       THEN Cases_on `(one_step_real (get_active_machine si) cycle <|proc := 0|>)`       THEN FULL_SIMP_TAC (srw_ss()) [read_cpsr_def, read__psr_def, readT_def]
       THEN Q.ABBREV_TAC `cond_intr = (si.machine1.psrs (0,CPSR)).I ∨ (si.machine2.psrs (0,CPSR)).I ∨   cycle > 0`
       THEN IF_CASES_TAC
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN Cases_on `q`
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN REPEAT (CASE_TAC THEN RW_TAC (srw_ss()) [] THEN RW_TAC (srw_ss()) [constant_other_parts_on_machine_update_lem]));


val constant_inactive_machine_lem = store_thm(
    "constant_inactive_machine_lem",
    `` (one_step_ideal si cycle <|proc:=0|> = (ValueState tb inext,rc,mode')) ==> 
          (((si.logical_component.active_machine = guest1)
           ==> (si.machine2 = inext.machine2)) 
        /\ ((si.logical_component.active_machine = guest2) 
           ==> (si.machine1 = inext.machine1)))``,
       FULL_SIMP_TAC (srw_ss()) [one_step_ideal_def,  LET_DEF, constTC_def, execute_instr_ideal_def, update_machine_def, errorTC_def]
       THEN Cases_on `(one_step_real (get_active_machine si) cycle <|proc := 0|>)`       THEN FULL_SIMP_TAC (srw_ss()) [read_cpsr_def, read__psr_def, readT_def]
       THEN Q.ABBREV_TAC `cond_intr = (si.machine1.psrs (0,CPSR)).I ∨ (si.machine2.psrs (0,CPSR)).I ∨   cycle > 0`
       THEN IF_CASES_TAC
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN Cases_on `q`
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN REPEAT (CASE_TAC THEN RW_TAC (srw_ss()) [you_and_me_thm] THEN RW_TAC (srw_ss()) [constant_other_parts_on_machine_update_lem]));



(***************  get from SIMILAR  to CORRECT_USER_MODE *******************)
;

val untouched_hypervisor_values_lem = (LIST_CONJ ( map ( fn address => 
                      UNDISCH_ALL (Q.prove(`((untouched guest1 sr rnext) \/ (untouched guest2 sr rnext)) ==> (read_mem32 (^address) rnext.memory = read_mem32 (^address) sr.memory)`,
                                        RW_TAC (srw_ss()) []
                                           THEN FULL_SIMP_TAC (srw_ss()) [read_mem32_def, untouched_def, guest1_min_adr_axiom, guest2_min_adr_axiom]
                                           THEN (PAT_ASSUM ``!(a:word32). X`` (fn th =>  ASSUME_TAC (SPEC ``^address`` th)
                                                                                    THEN ASSUME_TAC (SPEC ``^address + 1w`` th)
                                                                                    THEN ASSUME_TAC (SPEC ``^address + 2w`` th)
                                                                                   THEN ASSUME_TAC (SPEC ``^address + 3w`` th)))
                                           THEN FULL_SIMP_TAC (srw_ss()) [guest_current_mode_adr_def, guest1_def, guest2_def, msg_conent_adr_def, is_msg_adr_def]
                                           THEN FULL_SIMP_TAC (srw_ss()) hypervisor_constants_axioms)))
 [``global_curr_vm_add``,
  ``global_vm_0_add + o_virtual_machine__current_mode_state``,
  ``global_vm_1_add + o_virtual_machine__current_mode_state``,
  ``msg_content_adr guest1``,
  ``msg_content_adr guest2``,
  ``is_msg_adr guest1``,
  ``is_msg_adr guest2``,
  ``global_curr_vm_add``,
  ``guest_current_mode_adr guest1``,
  ``guest_current_mode_adr guest2``,
  ``guest1 + o_virtual_machine__mode_states + o_context__psr + t_hyper_mode_state_len``,
  ``guest1 + o_virtual_machine__mode_states + o_context__psr``,
  ``guest2 + o_virtual_machine__mode_states + o_context__psr + t_hyper_mode_state_len``,
  ``guest2 + o_virtual_machine__mode_states + o_context__psr``,
  ``guest1 + o_virtual_machine__mode_states + o_context__psr + t_hyper_mode_state_len + o_hyper_mode_state__ctx``,
  ``guest1 + o_virtual_machine__mode_states + o_context__psr + o_hyper_mode_state__ctx``,
  ``guest2 + o_virtual_machine__mode_states + o_context__psr + t_hyper_mode_state_len + o_hyper_mode_state__ctx``,
  ``guest2 + o_virtual_machine__mode_states + o_context__psr + o_hyper_mode_state__ctx``]));



val get_context_psrs_value_lem = store_thm(
    "get_context_psrs_value_lem",
    ``((untouched guest1 sr rnext) \/ (untouched guest2 sr rnext)) ==> 
      ((((guest_context_adr guest1 sr.memory) = (guest1 + o_virtual_machine__mode_states + t_hyper_mode_state_len))
     \/ ((guest_context_adr guest1 sr.memory) = (guest1 + o_virtual_machine__mode_states)))
      ==> 
      (get_context_psrs_value guest1 sr.memory
     = get_context_psrs_value guest1 rnext.memory))
 /\  ((((guest_context_adr guest2 sr.memory) = (guest2 + o_virtual_machine__mode_states + t_hyper_mode_state_len))
     \/ ((guest_context_adr guest2 sr.memory) = (guest2 + o_virtual_machine__mode_states)))
      ==> 
      (get_context_psrs_value guest2 sr.memory
     = get_context_psrs_value guest2 rnext.memory))``,
    RW_TAC (srw_ss())  [get_context_psrs_value_def]
       THEN AP_TERM_TAC
       THEN ((`cntxt = guest_context_adr guest1 sr.memory` by (IMP_RES_TAC (DISCH_ALL untouched_hypervisor_values_lem)
                                 THEN FULL_SIMP_TAC (srw_ss()) [guest_context_adr_def, LET_DEF] THEN NO_TAC))
             ORELSE 
             (`cntxt = guest_context_adr guest2 sr.memory` by (IMP_RES_TAC (DISCH_ALL untouched_hypervisor_values_lem)
                                 THEN FULL_SIMP_TAC (srw_ss()) [guest_context_adr_def, LET_DEF] THEN NO_TAC)))
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN IMP_RES_TAC (DISCH_ALL untouched_hypervisor_values_lem)
       THEN FULL_SIMP_TAC (srw_ss()) [guest_psr_adr_def, guest_context_adr_def, LET_DEF]
       THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []);



(* can be optimized *)
val untouched_hypervisor_register_values_lemmas = 
    (map ( fn offset =>
           LIST_CONJ ( map ( fn rnum =>
                      UNDISCH_ALL (Q.prove(`((untouched guest1 sr rnext) \/ (untouched guest2 sr rnext)) ==> (read_mem32 (guest_reg_adr (^offset) ^rnum) rnext.memory = read_mem32 (guest_reg_adr (^offset) ^rnum) sr.memory)`,
                                        RW_TAC (srw_ss()) []
                                           THEN FULL_SIMP_TAC (srw_ss()) [read_mem32_def, untouched_def, guest1_min_adr_axiom, guest2_min_adr_axiom]
                                           THEN (PAT_ASSUM ``!(a:word32). X`` (fn th =>  ASSUME_TAC (SPEC ``(guest_reg_adr (^offset) ^rnum)`` th)
                                                                                    THEN ASSUME_TAC (SPEC ``(guest_reg_adr (^offset) ^rnum) + 1w`` th)
                                                                                    THEN ASSUME_TAC (SPEC ``(guest_reg_adr (^offset) ^rnum) + 2w`` th)
                                                                                   THEN ASSUME_TAC (SPEC ``(guest_reg_adr (^offset) ^rnum) + 3w`` th)))
                                           THEN FULL_SIMP_TAC (srw_ss()) [guest_reg_adr_def, guest1_def, guest2_def, msg_conent_adr_def, is_msg_adr_def]
                                           THEN FULL_SIMP_TAC (srw_ss()) hypervisor_constants_axioms)))
                       [``0:num``, ``1:num``, ``2:num``, ``3:num``, ``4:num``, ``5:num``, ``6:num``, ``7:num``, ``8:num``, ``9:num``, ``10:num``, ``11:num``, ``12:num``, ``13:num``, ``14:num``, ``15:num``]))
         [``o_hyper_mode_state__ctx + o_virtual_machine__mode_states                           + guest1``,
          ``o_hyper_mode_state__ctx + o_virtual_machine__mode_states +  t_hyper_mode_state_len + guest1``,
          ``o_hyper_mode_state__ctx + o_virtual_machine__mode_states                           + guest2``,
          ``o_hyper_mode_state__ctx + o_virtual_machine__mode_states +  t_hyper_mode_state_len + guest2``,
          ``o_virtual_machine__mode_states +  t_hyper_mode_state_len + guest1``,
          ``o_virtual_machine__mode_states +  t_hyper_mode_state_len + guest2``,
          ``o_virtual_machine__mode_states                           + guest1``,
          ``o_virtual_machine__mode_states                           + guest2``]);



val [untouched_hypervisor_register_values_vm1_cntxt1_lem, untouched_hypervisor_register_values_vm1_cntxt2_lem, untouched_hypervisor_register_values_vm2_cntxt1_lem, untouched_hypervisor_register_values_vm2_cntxt2_lem, untouched_hypervisor_register_values_vm1_cntxt3_lem, untouched_hypervisor_register_values_vm2_cntxt3_lem, untouched_hypervisor_register_values_vm1_cntxt4_lem, untouched_hypervisor_register_values_vm2_cntxt4_lem] = untouched_hypervisor_register_values_lemmas;


fun similar_to_cus_gst AGST IGST INAM INIM SIAM SIIM = 
    (Q.prove (` (ARM_MODE rnext = 16w)                         ==> 
               (similar ^AGST rnext ^INAM)                     ==> 
               (untouched ^AGST sr rnext)                      ==> 
               (mode_mix ^INAM)                                ==>
               (mode_mix rnext)                                ==>
               (assert_mode 16w sr)                            ==> 
               (assert_mode 16w ^SIAM)                         ==>
               (^INIM = ^SIIM)                                 ==> 
               (inext.logical_component = si.logical_component)==>
               (correct_user_mode_states sr si ^AGST)          ==>  
               (correct_user_mode_states rnext inext ^AGST) `,
    (SIMP_TAC (bool_ss) [correct_user_mode_states_def, LET_DEF]
        THEN Q.ABBREV_TAC `hyp_inv_part_sr1 = ((guest_context_adr guest1 sr.memory =
                           guest1 + o_virtual_machine__mode_states + t_hyper_mode_state_len) ∨
                           (guest_context_adr guest1 sr.memory = guest1 + o_virtual_machine__mode_states))`
        THEN Q.ABBREV_TAC `hyp_inv_part_sr2 = ((guest_context_adr guest2 sr.memory =
                           guest2 + o_virtual_machine__mode_states + t_hyper_mode_state_len) ∨
                           (guest_context_adr guest2 sr.memory =  guest2 + o_virtual_machine__mode_states))`
        THEN RW_TAC (srw_ss()) [similar_def, LET_DEF, you_and_me_thm]
        THENL [ (* user mode *)
                FULL_SIMP_TAC (srw_ss()) [ARM_MODE_def, ARM_READ_CPSR_def],
                (* equal memory *)
                RW_TAC (srw_ss()) [guests_equal_memory_def]
                   THEN FULL_SIMP_TAC (srw_ss()) [guests_equal_memory_def, untouched_def, LET_DEF]
                   THEN SPEC_ASSUM_TAC (``!(a:word32). X``, [``a:word32``])
                   THEN FULL_SIMP_TAC (srw_ss()) [address_trans],
                (* active guest equal regs psrs *)
                RW_TAC (srw_ss()) [active_guest_equal_regs_psrs_def, user_regs_from_state_def, LET_DEF, read__reg_def, readT_def, user_regs_from_list_def, LookUp_UserRName_def, you_and_me_thm]
                   THEN FULL_SIMP_TAC (srw_ss()) [equal_user_register_def, you_and_me_thm],
                (* inactive guest equal regs psrs *)
                ASSUME_TAC get_context_psrs_value_lem
                   THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []
                   THEN UNABBREV_ALL_TAC
                   THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []
                   THEN RES_TAC
                   THEN FULL_SIMP_TAC (srw_ss()) [inactive_guest_equal_regs_psrs_def, you_and_me_thm, get_context_regs_value_def, LET_DEF]
                   THEN IMP_RES_TAC (DISCH_ALL untouched_hypervisor_register_values_vm1_cntxt3_lem)
                   THEN IMP_RES_TAC (DISCH_ALL untouched_hypervisor_register_values_vm1_cntxt4_lem)
                   THEN IMP_RES_TAC (DISCH_ALL untouched_hypervisor_register_values_vm2_cntxt3_lem)
                   THEN IMP_RES_TAC (DISCH_ALL untouched_hypervisor_register_values_vm2_cntxt4_lem)
                   THEN FULL_SIMP_TAC (srw_ss()) [guest_context_adr_def, LET_DEF]
                   THEN IMP_RES_TAC (DISCH_ALL untouched_hypervisor_values_lem)
                   THEN UNABBREV_ALL_TAC 
                   THEN UNDISCH_ALL_TAC 
                   THEN RW_TAC (srw_ss()) [you_and_me_thm],
                (* hypervisor constraints *)
                IMP_RES_TAC (DISCH_ALL untouched_hypervisor_values_lem)
                   THEN FULL_SIMP_TAC (srw_ss()) [hypervisor_constraints_def]
                   THEN RW_TAC (srw_ss()) []
                   THENL [FULL_SIMP_TAC (srw_ss()) [get_banked_context_regs_value_def, LET_DEF, guest_context_adr_def]
                            THEN IF_CASES_TAC
                            THEN FULL_SIMP_TAC (srw_ss()) []
                            THENL [IMP_RES_TAC (DISCH_ALL untouched_hypervisor_register_values_vm1_cntxt2_lem), 
                                   IMP_RES_TAC (DISCH_ALL untouched_hypervisor_register_values_vm1_cntxt1_lem)]
                            THEN FULL_SIMP_TAC (srw_ss()) [],
                          FULL_SIMP_TAC (srw_ss()) [get_banked_context_regs_value_def, LET_DEF, guest_context_adr_def]
                            THEN IF_CASES_TAC
                            THEN FULL_SIMP_TAC (srw_ss()) []
                            THENL [IMP_RES_TAC (DISCH_ALL untouched_hypervisor_register_values_vm2_cntxt2_lem), 
                                   IMP_RES_TAC (DISCH_ALL untouched_hypervisor_register_values_vm2_cntxt1_lem)]
                            THEN FULL_SIMP_TAC (srw_ss()) [],
                         FULL_SIMP_TAC (srw_ss()) [get_banked_context_psrs_value_def, LET_DEF, guest_psr_adr_def]
                            THEN REPEAT (IF_CASES_TAC THEN FULL_SIMP_TAC (srw_ss()) [])
                            THEN FULL_SIMP_TAC (srw_ss()) [guest_context_adr_def, LET_DEF]
                            THEN IMP_RES_TAC (DISCH_ALL untouched_hypervisor_values_lem)
                            THEN UNABBREV_ALL_TAC 
                            THEN UNDISCH_ALL_TAC 
                            THEN RW_TAC (srw_ss()) hypervisor_constants_axioms,
                          FULL_SIMP_TAC (srw_ss()) [get_banked_context_psrs_value_def, LET_DEF, guest_psr_adr_def]
                            THEN REPEAT (IF_CASES_TAC THEN FULL_SIMP_TAC (srw_ss()) [])
                            THEN FULL_SIMP_TAC (srw_ss()) [guest_context_adr_def, LET_DEF]
                            THEN IMP_RES_TAC (DISCH_ALL untouched_hypervisor_values_lem)
                            THEN UNABBREV_ALL_TAC 
                            THEN UNDISCH_ALL_TAC 
                            THEN RW_TAC (srw_ss()) hypervisor_constants_axioms],
                (* user mode constraints*)
                FULL_SIMP_TAC (srw_ss()) [user_mode_constraints_def, untouched_def, mode_mix_def, LET_DEF, assert_mode_def, similarity_implies_equal_mode_thm, you_and_me_thm, ARM_MODE_def, ARM_READ_CPSR_def]
                  THEN UNDISCH_ALL_TAC 
                  THEN RW_TAC (srw_ss()) [],
                (* coprocessor constraints *)
                FULL_SIMP_TAC (srw_ss()) [coprocessor_constrains_def]
                   THEN FULL_SIMP_TAC (srw_ss()) [untouched_def, LET_DEF]
                   THEN UNDISCH_ALL_TAC 
                   THEN RW_TAC (srw_ss()) [],
                (* 2 x partial Hyp Invariants *)
                FULL_SIMP_TAC (srw_ss()) [guest_context_adr_def, LET_DEF]
                   THEN IMP_RES_TAC (DISCH_ALL untouched_hypervisor_values_lem)
                   THEN UNABBREV_ALL_TAC 
                   THEN UNDISCH_ALL_TAC 
                   THEN RW_TAC (srw_ss()) [],
                FULL_SIMP_TAC (srw_ss()) [guest_context_adr_def, LET_DEF]
                   THEN IMP_RES_TAC (DISCH_ALL untouched_hypervisor_values_lem)
                   THEN UNABBREV_ALL_TAC 
                   THEN UNDISCH_ALL_TAC 
                   THEN RW_TAC (srw_ss()) []])));



val similar_to_cus_thm = CONJ
   (similar_to_cus_gst (``guest1``)  (``guest2``)  (``inext.machine1``)  (``inext.machine2``)  (``si.machine1``) (``si.machine2``))
   (similar_to_cus_gst (``guest2``)  (``guest1``)  (``inext.machine2``)  (``inext.machine1``)  (``si.machine2``) (``si.machine1``));



(***************  get from SIMILAR  to CORRECT_SWITCHED_MODE *******************)
;

fun similar_to_css_gst AGST IGST INAM INIM SIAM SIIM = 
    (Q.prove (`(ARM_MODE rnext <> 16w)                         ==> 
               (similar ^AGST rnext ^INAM)                     ==> 
               (untouched ^AGST sr rnext)                      ==> 
               (mode_mix ^INAM)                                ==>
               (mode_mix rnext)                                ==>
               (assert_mode 16w sr)                            ==> 
               (assert_mode 16w ^SIAM)                         ==>
               (^INIM = ^SIIM)                                 ==> 
               (inext.logical_component = si.logical_component)==>
               (priv_mode_constraints_v3 ^AGST sr rnext)       ==>
               (priv_mode_constraints_v3 ^AGST ^SIAM ^INAM)    ==>
               (priv_mode_similar ^AGST rnext ^INAM)           ==>
               (correct_user_mode_states sr si ^AGST)          ==>  
               (correct_switched_mode_states rnext inext sr si ^AGST)`,
   (SIMP_TAC (bool_ss) [correct_user_mode_states_def, correct_switched_mode_states_def, LET_DEF]
        THEN Q.ABBREV_TAC `hyp_inv_part_sr1 = ((guest_context_adr guest1 sr.memory =
                           guest1 + o_virtual_machine__mode_states + t_hyper_mode_state_len) ∨
                           (guest_context_adr guest1 sr.memory = guest1 + o_virtual_machine__mode_states))`
        THEN Q.ABBREV_TAC `hyp_inv_part_sr2 = ((guest_context_adr guest2 sr.memory =
                           guest2 + o_virtual_machine__mode_states + t_hyper_mode_state_len) ∨
                           (guest_context_adr guest2 sr.memory =  guest2 + o_virtual_machine__mode_states))`
        THEN RW_TAC (srw_ss()) [similar_def, LET_DEF, you_and_me_thm]
        THENL [ (* user mode *)
                FULL_SIMP_TAC (srw_ss()) [ARM_MODE_def, ARM_READ_CPSR_def],
                (* equal memory *)
                RW_TAC (srw_ss()) [guests_equal_memory_def]
                   THEN FULL_SIMP_TAC (srw_ss()) [guests_equal_memory_def, untouched_def, LET_DEF]
                   THEN SPEC_ASSUM_TAC (``!(a:word32). X``, [``a:word32``])
                   THEN FULL_SIMP_TAC (srw_ss()) [address_trans],
                (* active guest equal regs psrs *)
                RW_TAC (srw_ss()) [active_guest_equal_regs_psrs_def, user_regs_from_state_def, LET_DEF, read__reg_def, readT_def, user_regs_from_list_def, LookUp_UserRName_def, you_and_me_thm]
                   THEN FULL_SIMP_TAC (srw_ss()) [equal_user_register_def, you_and_me_thm],
                (* inactive guest equal regs psrs *)
                ASSUME_TAC get_context_psrs_value_lem
                   THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []
                   THEN UNABBREV_ALL_TAC
                   THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []
                   THEN RES_TAC
                   THEN FULL_SIMP_TAC (srw_ss()) [inactive_guest_equal_regs_psrs_def, you_and_me_thm, get_context_regs_value_def, LET_DEF]
                   THEN IMP_RES_TAC (DISCH_ALL untouched_hypervisor_register_values_vm1_cntxt3_lem)
                   THEN IMP_RES_TAC (DISCH_ALL untouched_hypervisor_register_values_vm1_cntxt4_lem)
                   THEN IMP_RES_TAC (DISCH_ALL untouched_hypervisor_register_values_vm2_cntxt3_lem)
                   THEN IMP_RES_TAC (DISCH_ALL untouched_hypervisor_register_values_vm2_cntxt4_lem)
                   THEN FULL_SIMP_TAC (srw_ss()) [guest_context_adr_def, LET_DEF]
                   THEN IMP_RES_TAC (DISCH_ALL untouched_hypervisor_values_lem)
                   THEN UNABBREV_ALL_TAC 
                   THEN UNDISCH_ALL_TAC 
                   THEN RW_TAC (srw_ss()) [you_and_me_thm],
                (* hypervisor constraints *)
                IMP_RES_TAC (DISCH_ALL untouched_hypervisor_values_lem)
                   THEN FULL_SIMP_TAC (srw_ss()) [hypervisor_constraints_def]
                   THEN RW_TAC (srw_ss()) []
                   THENL [FULL_SIMP_TAC (srw_ss()) [get_banked_context_regs_value_def, LET_DEF, guest_context_adr_def]
                            THEN IF_CASES_TAC
                            THEN FULL_SIMP_TAC (srw_ss()) []
                            THENL [IMP_RES_TAC (DISCH_ALL untouched_hypervisor_register_values_vm1_cntxt2_lem), 
                                   IMP_RES_TAC (DISCH_ALL untouched_hypervisor_register_values_vm1_cntxt1_lem)]
                            THEN FULL_SIMP_TAC (srw_ss()) [],
                          FULL_SIMP_TAC (srw_ss()) [get_banked_context_regs_value_def, LET_DEF, guest_context_adr_def]
                            THEN IF_CASES_TAC
                            THEN FULL_SIMP_TAC (srw_ss()) []
                            THENL [IMP_RES_TAC (DISCH_ALL untouched_hypervisor_register_values_vm2_cntxt2_lem), 
                                   IMP_RES_TAC (DISCH_ALL untouched_hypervisor_register_values_vm2_cntxt1_lem)]
                            THEN FULL_SIMP_TAC (srw_ss()) [],
                         FULL_SIMP_TAC (srw_ss()) [get_banked_context_psrs_value_def, LET_DEF, guest_psr_adr_def]
                            THEN REPEAT (IF_CASES_TAC THEN FULL_SIMP_TAC (srw_ss()) [])
                            THEN FULL_SIMP_TAC (srw_ss()) [guest_context_adr_def, LET_DEF]
                            THEN IMP_RES_TAC (DISCH_ALL untouched_hypervisor_values_lem)
                            THEN UNABBREV_ALL_TAC 
                            THEN UNDISCH_ALL_TAC 
                            THEN RW_TAC (srw_ss()) hypervisor_constants_axioms,
                          FULL_SIMP_TAC (srw_ss()) [get_banked_context_psrs_value_def, LET_DEF, guest_psr_adr_def]
                            THEN REPEAT (IF_CASES_TAC THEN FULL_SIMP_TAC (srw_ss()) [])
                            THEN FULL_SIMP_TAC (srw_ss()) [guest_context_adr_def, LET_DEF]
                            THEN IMP_RES_TAC (DISCH_ALL untouched_hypervisor_values_lem)
                            THEN UNABBREV_ALL_TAC 
                            THEN UNDISCH_ALL_TAC 
                            THEN RW_TAC (srw_ss()) hypervisor_constants_axioms],
                (* coprocessor constraints *)
                FULL_SIMP_TAC (srw_ss()) [coprocessor_constrains_def]
                   THEN FULL_SIMP_TAC (srw_ss()) [untouched_def, LET_DEF]
                   THEN UNDISCH_ALL_TAC 
                   THEN RW_TAC (srw_ss()) [],
                (* inactive guest intrpt flags *)
                FULL_SIMP_TAC (srw_ss()) [you_and_me_thm, inactive_guest_switched_mode_intrpt_flags_def, user_mode_constraints_def, LET_DEF]])));


val similar_to_css_thm = CONJ
   (similar_to_css_gst (``guest1``)  (``guest2``)  (``inext.machine1``)  (``inext.machine2``)  (``si.machine1``) (``si.machine2``))
   (similar_to_css_gst (``guest2``)  (``guest1``)  (``inext.machine2``)  (``inext.machine1``)  (``si.machine2``) (``si.machine1``));





(***************  User Lemma   *******************)


val USER_LEMMA_TAC =  RW_TAC (srw_ss()) []
       (* for every guest *)
       THENL (map (fn (AGST, IGST, INAM, INIM, SIAM, SIIM, IM)  =>
             (`(si.machine1.psrs (0,CPSR)).I = (si.machine2.psrs (0,CPSR)).I` by FULL_SIMP_TAC (srw_ss()) [correct_user_mode_states_def, user_mode_constraints_def, LET_DEF] 
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN `(sr.psrs (0,CPSR)).I = (si.machine1.psrs (0,CPSR)).I` by FULL_SIMP_TAC (srw_ss()) [correct_user_mode_states_def, user_mode_constraints_def, LET_DEF] 
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN `si.logical_component.active_machine = ^AGST` by FULL_SIMP_TAC (srw_ss()) [correct_user_mode_states_def, hypervisor_constraints_def, LET_DEF] 
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN Cases_on `one_step_ideal si cycle <|proc := 0|>` 
                  THEN Cases_on `r` 
                  THEN Cases_on `q` 
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  (* cases: none vs. some error in ideal mode *)
                  THENL (map (fn SIN =>
                        (IMP_RES_TAC constant_logical_component_lem
                           THEN Q.ABBREV_TAC `inext = (b:composite_arm_state)`
                           THEN IMP_RES_TAC constant_inactive_machine_lem
                           THEN FULL_SIMP_TAC (srw_ss()) [one_step_ideal_def, LET_DEF, execute_instr_ideal_def, read_cpsr_def, read__psr_def, readT_def, one_step_real_def, constTC_def, errorTC_def]
                           THEN Cases_on `(^SIAM.psrs (0,CPSR)).I <> (((^IM) (^SIN)).psrs (0,CPSR)).I`
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN Q.ABBREV_TAC  `ideal_intrpt_condition = cycle ≤ 0 ∧ ¬((get_active_machine si).psrs (0,CPSR)).I`
                           THEN Q.ABBREV_TAC `real_intrpt_cond = (cycle ≤ 0 ∧ (~((((^IM) (^SIN)).psrs (0,CPSR)).I)))`
                           THEN `ideal_intrpt_condition = real_intrpt_cond ` by  (UNABBREV_ALL_TAC THEN FULL_SIMP_TAC (srw_ss()) [get_active_machine_def, you_and_me_thm] THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [])
                           THEN FULL_SIMP_TAC (srw_ss()) [get_active_machine_def]
                           THEN Cases_on `^SIN.logical_component.active_machine = ^AGST` 
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN Cases_on `ideal_intrpt_condition` 
                           THEN FULL_SIMP_TAC (srw_ss()) [you_and_me_thm]
                           (* cases: hw_intrpt or no interrupt *)
                           THENL (map (fn INTRPTTYPE =>  
                                      (Cases_on `mmu_arm_next ^INTRPTTYPE ^SIAM` THEN FULL_SIMP_TAC (srw_ss()) []
                                        THEN FULL_SIMP_TAC (srw_ss()) [update_machine_def, you_and_me_thm]
                                        THEN TRY(`^INAM = b'` by (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [] THEN EVAL_TAC THEN NO_TAC))
                                        THEN IMP_RES_TAC cus_to_similar_thm
                                        THEN ASSUME_TAC (SPEC INTRPTTYPE (GEN_ALL mmu_arm_next_comb_thm))
                                        THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]
                                        THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``^AGST``, ``sr:arm_state``, ``(^SIAM):arm_state``])
                                        THEN RES_TAC
                                        THEN IMP_RES_TAC similarity_implies_equal_mode_thm
                                        THEN `(ARM_MODE ^SIAM ≠ 16w) = F` by FULL_SIMP_TAC (srw_ss()) []
                                        THEN (NTAC 2 (FULL_SIMP_TAC (srw_ss()) [priv_mode_similar_def, similarity_implies_equal_mode_thm, assert_mode_def]))
                                        THEN ASSUME_TAC (similar_to_cus_thm)
                                        THEN IMP_RES_TAC similarity_implies_equal_mode_thm
                                        THEN FULL_SIMP_TAC (srw_ss())  [assert_mode_def]
                                        THEN RW_TAC (srw_ss()) [gen_untouched_def]
                                        THEN FULL_SIMP_TAC (srw_ss()) [you_and_me_thm]
                                        THEN (REPEAT (IMP_RES_TAC untouched_mmu_setup_lem))))
                                 [``HW_Irq``,``NoInterrupt``]))) 
                        [``inext:composite_arm_state``, ``si:composite_arm_state``])))
             [((``guest1``),  (``guest2``),  (``inext.machine1``),  (``inext.machine2``),  (``si.machine1``) ,(``si.machine2``), (``composite_arm_state_machine2``)), ((``guest2``),  (``guest1``),  (``inext.machine2``),  (``inext.machine1``),  (``si.machine2``) ,(``si.machine1``), (``composite_arm_state_machine1``))]);





val user_mode_thm = store_thm(
    "user_mode_thm",
    ``! sr si cycle  ta rnext rc g .
    (((g=guest1) \/ (g=guest2)) /\ 
     (mmu_requirements sr g)    /\
     (mmu_requirements si.machine1 guest1)  /\
     (mmu_requirements si.machine2 guest2)  /\ 
     (correct_user_mode_states sr si g) /\
     (ARM_MODE sr = 0b10000w)    /\
     (one_step_real sr cycle  <|proc:=0|> = (ValueState ta rnext,rc)))
   ==>
    (? mode' tb inext .
    (one_step_ideal si cycle <|proc:=0|> = (ValueState tb inext,rc,mode')) /\
    ((ARM_MODE rnext = mode') /\ ((ARM_MODE rnext = 0b10000w) ==>
		((correct_user_mode_states rnext inext g ) /\
		(mmu_requirements rnext g)    /\
		(mmu_requirements inext.machine1 guest1)  /\
		(mmu_requirements inext.machine2 guest2) /\
                (gen_untouched sr si rnext inext g)))))``,
   USER_LEMMA_TAC);


val user_mode_error_thm = store_thm(
    "user_mode_error_thm",
    ``! sr si cycle g er rc .
    (((g=guest1) \/ (g=guest2)) /\ 
     (correct_user_mode_states sr si g ) /\
     (mmu_requirements sr g)    /\
     (mmu_requirements si.machine1 guest1)  /\
     (mmu_requirements si.machine2 guest2)  /\ 
     (ARM_MODE sr = 0b10000w)    /\
     (one_step_real sr cycle  <|proc:=0|>  = (Error er ,rc))
   )
   ==>
    (? ei ic mode'.( one_step_ideal si cycle  <|proc:=0|> = (Error ei,ic,mode')) /\ (er=ei))``,
    USER_LEMMA_TAC);

         

(***************  Switching Lemma   *******************)
;

val SWITCHING_LEMMA_TAC =  RW_TAC (srw_ss()) []
       (* for every guest *)
       THENL (map (fn (AGST, IGST, INAM, INIM, SIAM, SIIM, IM)  =>
             (`(si.machine1.psrs (0,CPSR)).I = (si.machine2.psrs (0,CPSR)).I` by FULL_SIMP_TAC (srw_ss()) [correct_user_mode_states_def, user_mode_constraints_def, LET_DEF] 
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN `(sr.psrs (0,CPSR)).I = (si.machine1.psrs (0,CPSR)).I` by FULL_SIMP_TAC (srw_ss()) [correct_user_mode_states_def, user_mode_constraints_def, LET_DEF] 
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN `si.logical_component.active_machine = ^AGST` by FULL_SIMP_TAC (srw_ss()) [correct_user_mode_states_def, hypervisor_constraints_def, LET_DEF] 
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN Cases_on `one_step_ideal si cycle <|proc := 0|>` 
                  THEN Cases_on `r` 
                  THEN Cases_on `q` 
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  (* cases: none vs. some error in ideal mode *)
                  THENL (map (fn SIN =>
                        (IMP_RES_TAC constant_logical_component_lem
                           THEN Q.ABBREV_TAC `inext = (b:composite_arm_state)`
                           THEN IMP_RES_TAC constant_inactive_machine_lem
                           THEN FULL_SIMP_TAC (srw_ss()) [one_step_ideal_def, LET_DEF, execute_instr_ideal_def, read_cpsr_def, read__psr_def, readT_def, one_step_real_def, constTC_def, errorTC_def]
                           THEN Cases_on `(^SIAM.psrs (0,CPSR)).I <> (((^IM) (^SIN)).psrs (0,CPSR)).I`
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN Q.ABBREV_TAC  `ideal_intrpt_condition = cycle ≤ 0 ∧ ¬((get_active_machine si).psrs (0,CPSR)).I`
                           THEN Q.ABBREV_TAC `real_intrpt_cond = (cycle ≤ 0 ∧ (~((((^IM) (^SIN)).psrs (0,CPSR)).I)))`
                           THEN `ideal_intrpt_condition = real_intrpt_cond ` by  (UNABBREV_ALL_TAC THEN FULL_SIMP_TAC (srw_ss()) [get_active_machine_def, you_and_me_thm] THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [])
                           THEN FULL_SIMP_TAC (srw_ss()) [get_active_machine_def]
                           THEN Cases_on `^SIN.logical_component.active_machine = ^AGST` 
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN Cases_on `ideal_intrpt_condition` 
                           THEN FULL_SIMP_TAC (srw_ss()) [you_and_me_thm]
                           (* cases: hw_intrpt or no interrupt *)
                           THENL (map (fn INTRPTTYPE =>  
                                      (Cases_on `mmu_arm_next ^INTRPTTYPE ^SIAM` THEN FULL_SIMP_TAC (srw_ss()) []
                                        THEN FULL_SIMP_TAC (srw_ss()) [update_machine_def, you_and_me_thm]
                                        THEN TRY(`^INAM = b'` by (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [] THEN EVAL_TAC THEN NO_TAC))
                                        THEN IMP_RES_TAC cus_to_similar_thm
                                        THEN ASSUME_TAC (SPEC INTRPTTYPE (GEN_ALL mmu_arm_next_comb_thm))
                                        THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]
                                        THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``^AGST``, ``sr:arm_state``, ``(^SIAM):arm_state``])
                                        THEN RES_TAC
                                        THEN IMP_RES_TAC similarity_implies_equal_mode_thm
                                        THEN `priv_mode_similar ^AGST sr ^SIAM` by FULL_SIMP_TAC (srw_ss()) [priv_mode_similar_def]
                                        THEN `(ARM_MODE ^SIAM ≠ 16w) = F` by FULL_SIMP_TAC (srw_ss()) []
                                        THEN (NTAC 2 (FULL_SIMP_TAC (srw_ss()) [similarity_implies_equal_mode_thm, assert_mode_def]))
                                        THEN ASSUME_TAC (similar_to_css_thm)
                                        THEN IMP_RES_TAC similarity_implies_equal_mode_thm
                                        THEN FULL_SIMP_TAC (srw_ss())  [assert_mode_def]
                                        THEN RW_TAC (srw_ss()) [gen_untouched_def]
                                        THEN FULL_SIMP_TAC (srw_ss()) [you_and_me_thm]
                                        THEN (REPEAT (IMP_RES_TAC untouched_mmu_setup_lem))))
                                 [``HW_Irq``,``NoInterrupt``]))) 
                        [``inext:composite_arm_state``, ``si:composite_arm_state``])))
             [((``guest1``),  (``guest2``),  (``inext.machine1``),  (``inext.machine2``),  (``si.machine1``) ,(``si.machine2``), (``composite_arm_state_machine2``)), ((``guest2``),  (``guest1``),  (``inext.machine2``),  (``inext.machine1``),  (``si.machine2``) ,(``si.machine1``), (``composite_arm_state_machine1``))]);





val switched_mode_thm = store_thm(
    "switched_mode_thm",
    ``!  sr si rnext cycle ra rc g .
    (((g=guest1) \/ (g=guest2)) /\ 
     (correct_user_mode_states sr si g ) /\
     (mmu_requirements sr g)    /\
     (mmu_requirements si.machine1 guest1)  /\
     (mmu_requirements si.machine2 guest2)  /\ 
     (ARM_MODE sr = 0b10000w)    /\
     (one_step_real sr cycle <|proc:=0|> = (ValueState ra rnext,rc)))
   ==>
    (? im ia inext .
    (one_step_ideal si cycle <|proc:=0|> = (ValueState ia inext,rc,im)) /\
    (im = ARM_MODE rnext) /\ ((im <> 0b10000w) ==>
       ((correct_switched_mode_states rnext inext sr si g ) /\
                (gen_untouched sr si rnext inext g))))``,
   SWITCHING_LEMMA_TAC);






