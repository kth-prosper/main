
(******************************************************************************)
(*                                                                            *)
(*                             THEOREMS                                       *)
(*                                                                            *)
(******************************************************************************)
val _ = augment_srw_ss [boolSimps.LET_ss];

val obs_bisimulation_rel_def = Define `obs_bisimulation_rel R id ii = 
 !rs is cycle. 
 let other_guest = if(id=guest1)
		   then
		       guest2
		   else
		       guest1
 in
     if (R (rs,cycle) (is,cycle) id) then
    ((mask_real rs id ii) = (mask_ideal is id ii)) /\
    (* (obs_equal rs is	 mask_real mask_ideal "vm1") /\ *)
    (* (obs_equal rs is	 mask_real mask_ideal "vm2")  /\  *)
   (
    (* perform one strong transition *) 
    let (rs_state,rc) = one_step_real rs cycle ii in 
    let (is_state,ic,im) = one_step_ideal is cycle ii in 
    case rs_state of
      ValueState ra rs' ->
       (case (is_state) of
     	  (ValueState ia is' ->
    	   let rm = ARM_MODE rs' in
            if (rm = 0b10000w) then
    	          ((R (rs',rc) (is',ic) id) /\ (im=rm) /\ (ic=rc)) 
	    (* both runs an unprivilaged instr  *)
            else  (* there is a weak transition *) 
              let (rw_state,rc',rm':bool[5])  = transform_state_real rs' rc id ii in 
              let (iw_state,ic',im':bool[5]) = transform_state_ideal is' ic im ii in 
               case rw_state of  
            	ValueState rc rs'' -> 
              	    (case iw_state of 
              	        ValueState ic is'' -> (rm = im) /\ (ic' = rc') /\
						(if (rm<>18w) 
						then 
						    (R (rs'',rc') (is'',ic') id)
						else
						    (R (rs'',rc') (is'',ic') other_guest))
				(* both handle the same exceprion/interupt *)
             	                || Error y -> F (*an error in ideal world while handling exp/int*)
             	     )
                || Error x -> 
             	    (case iw_state of
             	        ValueState id is'' -> F (*an error in real but not ideal world while handling exceptions/interupts*)
             	        ||  Error y -> (x=y) (*both got errors while handling exp/intr*))                 )
      	  || Error y -> F (*strong: real is successful but ideal gets an error*)
          	)
      || Error x ->
            (case (is_state) of 
              	 ValueState ib is' -> F
              	  || Error y -> (x=y))
      	   )
 else
     T`;

val obs_bisimilar_def = Define `obs_bisimilar state1 state2 id ii=
			?R.(obs_bisimulation_rel R id ii) /\ (R state1 state2 id)`;


val ASSUME_SPECL_TAC = 
fn l => fn thm => ASSUME_TAC (SPECL l thm);

val ASSUME_SIMP_TAC = 
fn l => fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) l thm);

val IMP_RES_SIMP_TAC = 
fn l => fn thm => IMP_RES_TAC (SIMP_RULE (srw_ss()) l thm);


val ASSUME_SPEC_TAC = 
fn l => fn thm => ASSUME_TAC (SPEC l thm);


val ASSUME_SPECL_SIMP_TAC = 
fn l => fn sthms => fn thm => ASSUME_TAC (SPECL l (SIMP_RULE (srw_ss()) sthms thm));

val IMP_RES_SPEC_TAC = 
fn l => fn thm => IMP_RES_TAC (SPEC l thm);

val IMP_RES_SPECL_TAC = 
fn l => fn thm => IMP_RES_TAC (SPECL l thm);

val MP_SPEC_TAC = 
fn l => fn thm => MP_TAC (SPEC l thm);

val MP_SPECL_TAC = 
fn l => fn thm => MP_TAC (SPECL l thm);

val ASSUME_SPECL_INST_TAC =  
 fn sl => fn tl => fn thm =>
	     ASSUME_TAC (SPECL sl (INST_TYPE tl thm)) 


val ASSUME_SPECL_GEN_REWRITE_TAC =
 fn (l , thm, simps) => ASSUME_TAC (SPECL 
					l (GEN_ALL (REWRITE_RULE simps thm)));



val correct_usermode_states_mode_assert_thm = store_thm(
  "correct_usermode_states_mode_assert_thm",
  ``!sr si cycle g.
   (((g=guest1) \/ (g=guest2)) /\
    (correct_user_mode_states sr si g)) ==>
    ((ARM_MODE sr = 16w)  /\
     (ARM_MODE si.machine1 = 16w) /\
     (ARM_MODE si.machine2 = 16w)) ``,
 FULL_SIMP_TAC (srw_ss()) [correct_user_mode_states_def,unique_guest_def] THEN
(RW_TAC (let_ss) []) THEN FULL_SIMP_TAC (srw_ss()) []);


val mmu_setup_implies_mmu_req_thm = new_axiom 
("mmu_setup_implies_mmu_req_thm", 
``! real g. ((g=guest1) \/ (g=guest2)) ==>
   mmu_coprocessor_setup real g ==>
   mmu_boot_setup real ==>
   mmu_requirements real g``);


val untouched_imp_outer_user_constraints_thm = store_thm(
  "untouched_imp_outer_user_constraints_thm",
``! rs rs' is is' g.
 outer_user_mode_constraints rs is g ==>
(ARM_MODE rs = 0b10000w) ==>
gen_untouched rs is rs' is' g ==>
(ARM_MODE rs' = 0b10000w)==>
(ARM_MODE is.machine1 = 16w) ==>
 (ARM_MODE is'.machine1 = 16w) ==>
(ARM_MODE is.machine2 = 16w) ==>
 (ARM_MODE is'.machine2 = 16w) ==>
outer_user_mode_constraints rs' is' g``,
  FULL_SIMP_TAC (srw_ss()) [outer_user_mode_constraints_def,
			    gen_untouched_def,untouched_def]
		THEN RW_TAC (srw_ss()) []);


val untouched_imp_real_coproc_setup_thm = 
store_thm ("untouched_imp_real_coproc_setup_thm", 
``!  rs is rs' is' g . 
gen_untouched rs is rs' is' g ==>
mmu_coprocessor_setup rs g ==>
mmu_coprocessor_setup rs' g``
,
FULL_SIMP_TAC (srw_ss()) [gen_untouched_def,
			  mmu_coprocessor_setup_def,
			  untouched_def]
	      THEN RW_TAC (srw_ss()) []
);

val untouched_imp_ideal_coproc_setup_thm = 
store_thm ("untouched_imp_ideal_coproc_setup_thm", 
``!  rs is rs' is' g . 
gen_untouched rs is rs' is' g ==>
((mmu_coprocessor_setup is.machine2 guest2 ==>
  mmu_coprocessor_setup is'.machine2 guest2) /\
 (mmu_coprocessor_setup is.machine1 guest1 ==>
  mmu_coprocessor_setup is'.machine1 guest1))``
,
FULL_SIMP_TAC (srw_ss()) [gen_untouched_def,
			  mmu_coprocessor_setup_def,
			  untouched_def]
THEN RW_TAC (srw_ss()) []
);


val untouched_imp_uncchanged_pt_thm = new_axiom 
("untouched_imp_uncchanged_pt_thm", 
 ``!  rs is rs' is' g. 
  gen_untouched rs is rs' is' g ==>
   ( boot_pt_unchanged rs rs' /\
     boot_pt_unchanged is.machine2 is'.machine2 /\
     boot_pt_unchanged is.machine1 is'.machine1)
``);

val untouched_mem_imp_kth_invars_thm = new_axiom 
("untouched_mem_imp_kth_invars_thm", 
``!state1 g state2. 
   kth_hyp_invariants state1 ==>
    (∀a.
        (g ≠ guest1 ∧ g ≠ guest2 ⇒
         (state1.memory a = state2.memory a)) ∧
        ((g = guest1) ∧ (a >₊ guest1_max_adr ∨ a <₊ guest1_min_adr) ⇒
         (state1.memory a = state2.memory a)) ∧
        ((g = guest2) ∧ (a >₊ guest2_max_adr ∨ a <₊ guest2_min_adr) ⇒
         (state1.memory a = state2.memory a)))
     ==>
     kth_hyp_invariants state2``
);


val gen_untouched_imp_kth_invars_thm = store_thm ("gen_untouched_imp_kth_invars_thm", 
``! rs is rs' is' g. 
  ((g=guest1) \/ (g=guest2)) ==>
  kth_hyp_invariants rs ==>
  gen_untouched rs is rs' is' g ==>
  kth_hyp_invariants rs'``,
 let val prove_lem = 
      fn gst =>
	 PAT_ASSUM ``untouched ^gst rs rs'`` 
		   (fn thm=> ASSUME_TAC (SIMP_RULE (let_ss) [untouched_def] thm))
		   THEN RW_TAC (srw_ss()) []
		   THEN IMP_RES_TAC  untouched_mem_imp_kth_invars_thm
		   THEN PAT_ASSUM ``!state2 g.X`` (fn thm => ASSUME_SPECL_TAC [``rs':arm_state``,
									       gst] thm)
		   THEN METIS_TAC []
 in
     RW_TAC (srw_ss()) [gen_untouched_def]
	    THEN FULL_SIMP_TAC (srw_ss()) []
	    THENL [prove_lem ``guest1``, prove_lem ``guest2``]
 end
);


val outer_user_mode_thm = store_thm 
("outer_user_mode_thm", `` 
    ! rs rs' is  cycle ra rc g .
   (((g=guest1) \/ (g=guest2)) /\ 
    (correct_user_mode_states rs is g) /\
    (outer_user_mode_constraints rs is g) /\
    (kth_hyp_invariants rs) /\
    (mmu_boot_setup rs) /\
    (mmu_boot_setup is.machine1) /\
    (mmu_boot_setup is.machine2) /\
    (mmu_coprocessor_setup rs g) /\
    (mmu_coprocessor_setup is.machine1 guest1) /\
    (mmu_coprocessor_setup is.machine2 guest2) /\
    (ARM_MODE rs = 0b10000w)    /\
    (one_step_real rs cycle  <|proc:=0|> = (ValueState ra rs',rc)))
   ==>
    (? im ib is' .
    (one_step_ideal is cycle <|proc:=0|> = (ValueState ib is',rc,im)) /\
    ((ARM_MODE rs' = im) /\ ((ARM_MODE rs' = 0b10000w) ==>
		((correct_user_mode_states rs' is' g ) /\
		(outer_user_mode_constraints rs' is' g) /\
    (kth_hyp_invariants rs') /\
    (mmu_boot_setup rs') /\
    (mmu_boot_setup is'.machine1) /\
    (mmu_boot_setup is'.machine2) /\
    (mmu_coprocessor_setup rs' g) /\
    (mmu_coprocessor_setup is'.machine1 guest1) /\
    (mmu_coprocessor_setup is'.machine2 guest2)
    ))))
 ``,
 RW_TAC (srw_ss()) []
	THEN IMP_RES_TAC user_mode_thm
	THEN FULL_SIMP_TAC (srw_ss()) []
	THEN ASSUME_SPECL_TAC [``rs:arm_state``, ``guest1``] mmu_setup_implies_mmu_req_thm
	THEN ASSUME_SPECL_TAC [``rs:arm_state``, ``guest2``] mmu_setup_implies_mmu_req_thm
	THEN ASSUME_SPECL_TAC [`` is.machine2:arm_state``, ``guest2``] mmu_setup_implies_mmu_req_thm
	THEN ASSUME_SPECL_TAC [`` is.machine1:arm_state``, ``guest1``] mmu_setup_implies_mmu_req_thm
	THEN FULL_SIMP_TAC (srw_ss()) []
	THEN RES_TAC
	THEN FULL_SIMP_TAC (srw_ss()) []
	THEN RW_TAC (srw_ss()) []
	THEN FULL_SIMP_TAC (srw_ss()) []
	THEN WEAKEN_TAC is_imp
	THEN FIRST_PROVE
	[
	 IMP_RES_TAC correct_usermode_states_mode_assert_thm
		     THEN FULL_SIMP_TAC (srw_ss()) []
		     THEN IMP_RES_TAC  untouched_imp_outer_user_constraints_thm
       ,
       IMP_RES_TAC untouched_imp_uncchanged_pt_thm
		   THEN IMP_RES_TAC mmu_if_mem_unchanged
       ,
       IMP_RES_TAC untouched_imp_ideal_coproc_setup_thm
       ,
       IMP_RES_TAC untouched_imp_real_coproc_setup_thm
       ,
       ASSUME_SPECL_TAC   [``rs:arm_state``,``is:composite_arm_state``,
			   ``rs':arm_state``,``inext:composite_arm_state``, 
			   ``guest1``]  gen_untouched_imp_kth_invars_thm
			  THEN RW_TAC (srw_ss()) []
       ,
       ASSUME_SPECL_TAC   [``rs:arm_state``,``is:composite_arm_state``,
			   ``rs':arm_state``,``inext:composite_arm_state``, 
			   ``guest2``]  gen_untouched_imp_kth_invars_thm
			  THEN RW_TAC (srw_ss()) []
	]
);



val outer_switched_mode_thm = store_thm 
("outer_switched_mode_thm", `` 
    ! rs rs' is ra cycle  rc g .
   (((g=guest1) \/ (g=guest2)) /\ 
    (correct_user_mode_states rs is g) /\
    (outer_user_mode_constraints rs is g) /\
    (kth_hyp_invariants rs) /\
    (mmu_boot_setup rs) /\
    (mmu_boot_setup is.machine1) /\
    (mmu_boot_setup is.machine2) /\
    (mmu_coprocessor_setup rs g) /\
    (mmu_coprocessor_setup is.machine1 guest1) /\
    (mmu_coprocessor_setup is.machine2 guest2) /\
    (ARM_MODE rs = 0b10000w)    /\
    (one_step_real rs cycle  <|proc:=0|> = (ValueState ra rs',rc)))
   ==>
    (? im ib is' .
    (one_step_ideal is cycle <|proc:=0|> = (ValueState ib is',rc,im)) /\
    ((ARM_MODE rs' = im) /\ ((ARM_MODE rs' <> 0b10000w) ==>
    ((correct_switched_mode_states rs' is' rs is g ) /\
     (outer_user_mode_constraints rs is g) /\
    (kth_hyp_invariants rs') /\
    (mmu_boot_setup rs') /\
    (mmu_boot_setup is'.machine1) /\
    (mmu_boot_setup is'.machine2) /\
    (mmu_coprocessor_setup rs' g) /\
    (mmu_coprocessor_setup is'.machine1 guest1) /\
    (mmu_coprocessor_setup is'.machine2 guest2)
    ))))
 ``,
RW_TAC (srw_ss()) []
	THEN ASSUME_SPECL_TAC [``rs:arm_state``, ``guest1``] mmu_setup_implies_mmu_req_thm
	THEN ASSUME_SPECL_TAC [``rs:arm_state``, ``guest2``] mmu_setup_implies_mmu_req_thm
	THEN ASSUME_SPECL_TAC [`` is.machine2:arm_state``, ``guest2``] mmu_setup_implies_mmu_req_thm
	THEN ASSUME_SPECL_TAC [`` is.machine1:arm_state``, ``guest1``] mmu_setup_implies_mmu_req_thm
	THEN FULL_SIMP_TAC (srw_ss()) []
	THEN RES_TAC
	THEN FULL_SIMP_TAC (srw_ss()) []
	THEN RW_TAC (srw_ss()) []
	THEN IMP_RES_TAC switched_mode_thm
	THEN FULL_SIMP_TAC (srw_ss()) []
	THEN (REPEAT (WEAKEN_TAC is_forall))
	THEN RW_TAC (srw_ss()) []
	THEN FULL_SIMP_TAC (srw_ss()) []
	THEN FIRST_PROVE
	[
       IMP_RES_TAC untouched_imp_uncchanged_pt_thm
		   THEN IMP_RES_TAC mmu_if_mem_unchanged
       ,
       IMP_RES_TAC untouched_imp_real_coproc_setup_thm
       ,
       IMP_RES_TAC untouched_imp_ideal_coproc_setup_thm
       ,
       ASSUME_SPECL_TAC   [``rs:arm_state``,``is:composite_arm_state``,
			   ``rs':arm_state``,``is':composite_arm_state``, 
			   ``guest1``]  gen_untouched_imp_kth_invars_thm
			  THEN RW_TAC (srw_ss()) []
       ,
       ASSUME_SPECL_TAC   [``rs:arm_state``,``is:composite_arm_state``,
			   ``rs':arm_state``,``is':composite_arm_state``, 
			   ``guest2``]  gen_untouched_imp_kth_invars_thm
			  THEN RW_TAC (srw_ss()) []
	]

);



val candidate_relation_def = 
    Define `candidate_relation (sr,c:int) (si,c':int) g  =
     outer_full_relation_user sr si g
`;


val bisimilar_eq_observation_thm = Define `bisimilar_eq_observation =
!s s' n g .
  (candidate_relation (s,n) (s',n) g )
==>
  (((mask_real s guest1) = (mask_ideal s' guest1)) /\
   ((mask_real s guest2) = (mask_ideal s' guest2))) `;


val bisimilar_correct_usermode_states = store_thm (
  "bisimilar_correct_usermode_states",
  ``!sr si cycle g.
   (((g=guest1) \/ (g=guest2)) /\
    (candidate_relation (sr,cycle) (si,cycle) g)) ==>
    (outer_full_relation_user sr si g) ``,
  FULL_SIMP_TAC (srw_ss()) [candidate_relation_def,correct_user_mode_states_def,
			  outer_full_relation_user_def]);

val bisimilar_mode_assert_thm = store_thm(
  "bisimilar_mode_assert_thm",
  ``!sr si cycle g.
   (((g=guest1) \/ (g=guest2)) /\
    (candidate_relation (sr,cycle) (si,cycle)) g) ==>
    ((ARM_MODE sr =  16w)  /\
     (ARM_MODE si.machine1 = 16w) /\
     (ARM_MODE si.machine2 = 16w)) ``,
 (FULL_SIMP_TAC (srw_ss()) [candidate_relation_def,
			  outer_full_relation_user_def,
			  correct_user_mode_states_def]) );

val correct_usermode_bisimilar_states_thm = store_thm(
  "correct_usermode_bisimilar_states_thm",
  ``!sr si cycle g .
   (((g=guest1) \/ (g=guest2)) /\
    (correct_user_mode_states sr si g ) /\
     (outer_user_mode_constraints sr si g)
  /\  (kth_hyp_invariants sr)
  /\  (mmu_boot_setup sr)
  /\  (mmu_boot_setup si.machine1)
  /\  (mmu_boot_setup si.machine2)
  /\  (mmu_coprocessor_setup sr g)
  /\  (mmu_coprocessor_setup si.machine1 guest1)
  /\  (mmu_coprocessor_setup si.machine2 guest2) ) ==>
    (candidate_relation (sr,cycle) (si,cycle) g) ``,
  FULL_SIMP_TAC (srw_ss()) [candidate_relation_def,
			outer_full_relation_user_def,
			correct_user_mode_states_def]
	);



val super_mode_thm = 
    new_axiom ("super_mode_thm", `` 
	      ! rs is rs' is'  is''  
	        ia ic ic' g im im' .
	                  ( ((g=guest1) \/ (g=guest2)) /\
			    (correct_switched_mode_states rs' is' rs is g ) /\
  			    (outer_user_mode_constraints rs is g)     	/\
			    (kth_hyp_invariants rs')			/\
			    (mmu_boot_setup rs')			/\
			    (mmu_boot_setup is'.machine1)		/\
			    (mmu_boot_setup is'.machine2)		/\
			    (mmu_coprocessor_setup rs' g)		/\
			    (mmu_coprocessor_setup is'.machine1 guest1)	/\
			    (mmu_coprocessor_setup is'.machine2 guest2)	/\
                            (transform_state_ideal is' ic im <|proc:=0|> = 
			         (ValueState ia is'', ic' ,im'))
 			    )
			   ==>
			   (? ra rs'' rc' .
			    (transform_state_real rs' ic g <|proc:=0|> = 
			           (ValueState ra rs'', ic' ,im'))
			      /\
			    (im' = 0b10000w) /\ 
			    (kth_hyp_invariants rs'')			  /\
			    (mmu_boot_setup rs'')			  /\
			    (mmu_boot_setup is''.machine1)		  /\
			    (mmu_boot_setup is''.machine2)		  /\
			    (mmu_coprocessor_setup is''.machine1 guest1)  /\
			    (mmu_coprocessor_setup is''.machine2 guest2)  /\
                            (if (g=guest1) 
			     then
				 access_violation rs'' = access_violation is''.machine1
			     else
				 access_violation rs'' = access_violation is''.machine2)
			    /\
			  (let g'= if (ARM_MODE rs' <>18w) 
				   then g else (if(g=guest1) then guest2 else guest1)
			   in
			    (correct_user_mode_states rs'' is'' g' ) /\
                            (outer_user_mode_constraints rs'' is'' g')     /\
			    (mmu_coprocessor_setup rs'' g')		  /\
			    (user_mode_constraints rs'' is'' g')))
			  ``); 


val super_mode_error_thm = 
    new_axiom ("super_mode_error_thm", `` 
	      ! rs is rs' is' ie c c' g im im'.
	      (
	    ((g=guest1) \/ (g=guest2)) /\
	    (correct_switched_mode_states  rs' is' rs
					   is g ) /\
			    (outer_user_mode_constraints rs is g)     	/\
			    (kth_hyp_invariants rs')			/\
			    (mmu_boot_setup rs')			/\
			    (mmu_boot_setup is'.machine1)		/\
			    (mmu_boot_setup is'.machine2)		/\
			    (mmu_coprocessor_setup rs' g)		/\
			    (mmu_coprocessor_setup is'.machine1 guest1)	/\
			    (mmu_coprocessor_setup is'.machine2 guest2)	/\
	    (transform_state_ideal is' c im  <|proc:=0|> = 
		 (Error ie, c' ,im'))
	    )
	   ==>
	   (? re rc' rm' .
	      (transform_state_real rs' c g <|proc:=0|> = 
		   (Error re, c' ,rm'))
	       /\
	      (re =ie))
	  ``);

val usermode_valid_cur_vm_thm = store_thm(
  "usermode_valid_cur_vm_thm",
``! rs is g. (correct_user_mode_states rs is g) ==>
(read_mem32 global_curr_vm_add rs.memory = g) ``
,
RW_TAC (srw_ss()) [correct_user_mode_states_def,
hypervisor_constraints_def]);


val usermode_have_same_active_regs_thm = store_thm(
  "usermode_have_same_active_regs_thm",
``! rs is g. 
(unique_guest g) ==>
(correct_user_mode_states rs is g) ==>
 ( user_regs_from_state rs <|proc := 0|> =
   user_regs_from_state (if (g=guest1) then is.machine1 else is.machine2) <|proc := 0|>)``,
RW_TAC (srw_ss()) [unique_guest_def]
THEN FULL_SIMP_TAC (srw_ss()) [correct_user_mode_states_def,
			       active_guest_equal_regs_psrs_def,
			       global_vm_0_add_axiom,
			       global_vm_1_add_axiom,
			       guest1_def,guest2_def]
);

val usermode_have_same_inactive_regs_thm = store_thm(
  "usermode_have_same_inactive_regs_thm",
``! rs is g. 
(unique_guest g) ==>
(correct_user_mode_states rs is g) ==>
 (user_regs_from_list
  (TAKE 16 (get_context_regs_value (if (g=guest2) then guest1 else guest2) rs.memory)) =
user_regs_from_state (if (g=guest2) then is.machine1 else is.machine2) <|proc := 0|>)``,
  RW_TAC (srw_ss()) [correct_user_mode_states_def,unique_guest_def]
	 THEN FULL_SIMP_TAC (srw_ss()) [inactive_guest_equal_regs_psrs_def,
					user_regs_from_list_def,global_vm_0_add_axiom,
					global_vm_1_add_axiom,
					guest1_def,guest2_def]
);


val usermode_have_same_cpsr_thm = store_thm(
  "usermode_have_same_cpsr_thm",
``! rs is g. 
(unique_guest g) ==>
(correct_user_mode_states rs is g) ==>
 ( rs.psrs (0,CPSR) = (if (g=guest1) then is.machine1 else is.machine2).psrs (0,CPSR))``,
  RW_TAC (srw_ss()) [correct_user_mode_states_def,unique_guest_def]
	 THEN FULL_SIMP_TAC (srw_ss()) [active_guest_equal_regs_psrs_def,
					global_vm_0_add_axiom,
					global_vm_1_add_axiom,
					guest1_def,guest2_def]
);

val usermode_have_same_inactive_cpsr_thm = store_thm(
  "usermode_have_same_inactive_cpsr_thm",
``! rs is g. 
(unique_guest g) ==>
(correct_user_mode_states rs is g) ==>
 (get_context_psrs_value (if (g=guest2) then guest1 else guest2) rs.memory = (if (g=guest2) then is.machine1 else is.machine2).psrs (0,CPSR))``,
  RW_TAC (srw_ss()) [correct_user_mode_states_def,unique_guest_def]
	 THEN FULL_SIMP_TAC (srw_ss()) [inactive_guest_equal_regs_psrs_def,
					get_context_psrs_value_def,global_vm_0_add_axiom,
					global_vm_1_add_axiom,
					guest1_def,guest2_def]
	
);


val usermode_have_same_memory_thm = store_thm(
  "usermode_have_same_memory_thm",
``! rs is g. 
(unique_guest g) ==>
(correct_user_mode_states rs is g) ==>
 (get_guest_mem g rs.memory =
  get_guest_mem g (if (g=guest1) then is.machine1 else is.machine2).memory )``,
  RW_TAC (srw_ss()) [correct_user_mode_states_def,unique_guest_def]
	 THEN FULL_SIMP_TAC (srw_ss()) [guests_equal_memory_def,
					get_guest_mem_def,
					global_vm_0_add_axiom,
					global_vm_1_add_axiom,
					guest1_def,guest2_def]
	 THEN RW_TAC (srw_ss()) []
);


val usermode_have_same_inactive_memory_thm = store_thm(
  "usermode_have_same_inactive_memory_thm",
``! rs is g. 
(unique_guest g) ==>
(correct_user_mode_states rs is g) ==>
(get_guest_mem (if (g=guest2) then guest1 else guest2) rs.memory =
  get_guest_mem (if (g=guest2) then guest1 else guest2) (if (g=guest1) then is.machine2 else is.machine1).memory )
``,
  RW_TAC (srw_ss()) [correct_user_mode_states_def,unique_guest_def]
	 THEN FULL_SIMP_TAC (srw_ss()) [guests_equal_memory_def,	
					get_guest_mem_def]
	 THEN RW_TAC (srw_ss()) [correct_user_mode_states_def,unique_guest_def]
);



val related_states_have_same_obs_thm = store_thm(
  "related_states_have_same_obs_thm",
``! rs is g cycle. (unique_guest g) ==>
  (candidate_relation (rs,cycle) (is,cycle) g) ==>
  (mask_real rs g <|proc := 0|> = mask_ideal is g <|proc := 0|>)``,

FULL_SIMP_TAC (srw_ss()) [candidate_relation_def,
			     outer_full_relation_user_def]
THEN RW_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) [mask_real_def, mask_ideal_def]
THEN RW_TAC (srw_ss()) []
THEN FIRST_PROVE [
ASSUME_SPECL_TAC [``rs:arm_state``,
		      ``is:composite_arm_state``,
		     ``guest1``] usermode_have_same_active_regs_thm
THEN FULL_SIMP_TAC (srw_ss()) [],
ASSUME_SPECL_TAC [``rs:arm_state``,
		      ``is:composite_arm_state``,
		     ``guest1``] usermode_have_same_cpsr_thm
THEN FULL_SIMP_TAC (srw_ss()) []
,
ASSUME_SPECL_TAC [``rs:arm_state``,
		      ``is:composite_arm_state``,
		     ``guest1``] usermode_have_same_memory_thm
THEN FULL_SIMP_TAC (srw_ss()) [get_guest_mem_def]
THEN RW_TAC (srw_ss()) [],
ASSUME_SPECL_TAC [``rs:arm_state``,
		      ``is:composite_arm_state``,
		     ``guest2``] usermode_have_same_active_regs_thm
THEN FULL_SIMP_TAC (srw_ss()) [unique_guest_def]
THEN METIS_TAC []
,
ASSUME_SPECL_TAC [``rs:arm_state``,
		      ``is:composite_arm_state``,
		     ``guest2``] usermode_have_same_cpsr_thm
THEN FULL_SIMP_TAC (srw_ss()) [unique_guest_def]
THEN METIS_TAC []
,
ASSUME_SPECL_TAC [``rs:arm_state``,
		      ``is:composite_arm_state``,
		     ``guest2``] usermode_have_same_memory_thm
THEN FULL_SIMP_TAC (srw_ss()) [get_guest_mem_def,unique_guest_def]
THEN METIS_TAC []
,
IMP_RES_TAC usermode_valid_cur_vm_thm]);
