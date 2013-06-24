(********************************************************************)
(*          The definitions of user,swithing,super mode lemmas
            as well as the definition of candidate relation 
				Narges                              *)
(********************************************************************)


val let_ss = simpLib.mk_simpset [boolSimps.LET_ss];
val words_ss = simpLib.mk_simpset [wordsLib.WORD_ss];
val let_bool_ss = simpLib.++ (bossLib.bool_ss , boolSimps.LET_ss);

val guests_equal_memory_def = Define `guests_equal_memory state1 state2 =
(! a.
 (((a <=+ (*UNSIGNED*) guest1_max_adr) /\ (a >=+ (*UNSIGNED*) guest1_min_adr)) ==>
        ((state1.memory a) = (state2.machine1.memory a)))
   /\
 (((a <=+ (*UNSIGNED*) guest2_max_adr) /\ (a >=+ (*UNSIGNED*) guest2_min_adr)) ==>
        ((state1.memory a) = (state2.machine2.memory a))))
`;

(* id: active guest *)
val active_guest_equal_regs_psrs_def =  Define `active_guest_equal_regs_psrs state1 state2 id  =
if (id = guest1) then
 ( 
   (state1.psrs (0,CPSR)= state2.machine1.psrs (0,CPSR)) /\ 
    (user_regs_from_state state1 <|proc:=0|> = user_regs_from_state state2.machine1 <|proc:=0|>))
else
 ((state1.psrs (0, CPSR)= state2.machine2.psrs (0,CPSR)) /\ 
    (user_regs_from_state state1 <|proc:=0|> = user_regs_from_state state2.machine2 <|proc:=0|>))
`;

(*id: the incative guest *)
val inactive_guest_equal_regs_psrs_def =  Define `inactive_guest_equal_regs_psrs state1 state2 id =
if (id=guest1) then
    ((get_context_psrs_value guest1 state1.memory = 
           (state2.machine1.psrs (0, CPSR)))
          /\
     (user_regs_from_list (TAKE 16 (get_context_regs_value guest1 state1.memory))                                          =  
     (user_regs_from_state (state2.machine1) <|proc:=0|> ))
   )
else
    ((get_context_psrs_value guest2 state1.memory = 
            (state2.machine2.psrs (0, CPSR))) 
          /\
     (user_regs_from_list (TAKE 16 (get_context_regs_value guest2 state1.memory))                                            =  user_regs_from_state state2.machine2 <|proc:=0|>)
   )`;



val hypervisor_constraints_def = Define `hypervisor_constraints sr si g =
  (read_mem32 global_curr_vm_add sr.memory = g) /\
  (si.logical_component.active_machine = g) /\
  (read_mem32 global_curr_vm_add sr.memory = si.logical_component.active_machine) /\
  (read_mem32 (msg_content_adr guest1) sr.memory = si.logical_component.message_box1) /\
  (read_mem32 (msg_content_adr guest2) sr.memory = si.logical_component.message_box2) /\
  ((read_mem32 (is_msg_adr guest1) sr.memory <> 0w) = si.logical_component.box_full1) /\
  ((read_mem32 (is_msg_adr guest2) sr.memory <> 0w) = si.logical_component.box_full2) /\
  ((read_mem32 (global_vm_0_add+o_virtual_machine__current_mode_state) sr.memory =  
    global_vm_0_add+o_virtual_machine__mode_states+t_hyper_mode_state_len) = 
   si.logical_component.ready1)/\
  ((read_mem32 (global_vm_1_add+o_virtual_machine__current_mode_state) sr.memory =  
    global_vm_1_add+o_virtual_machine__mode_states+t_hyper_mode_state_len) = si.logical_component.ready2) 
/\

 (user_regs_from_list (TAKE 16 (get_banked_context_regs_value guest1 sr.memory))                                            =  
     ( si.logical_component.context1.registers))
/\

 (user_regs_from_list (TAKE 16 (get_banked_context_regs_value guest2 sr.memory))                                            =  
     ( si.logical_component.context2.registers))	
/\
     (si.logical_component.context1.spsr = get_banked_context_psrs_value guest1 sr.memory)
/\
     (si.logical_component.context2.spsr = get_banked_context_psrs_value guest2 sr.memory)`;


val user_mode_constraints_def = 
    Define `user_mode_constraints sr si g =
    let active_machine = 
	if(g=guest1)
	then
	    si.machine1
	else
	    si.machine2
    in
     (sr.interrupt_wait 0 = active_machine.interrupt_wait 0)   
     /\
     (sr.information = active_machine.information)      
     /\
     (sr.monitors = active_machine.monitors)     
     /\
     (sr.event_register = active_machine.event_register)
     /\
     ((sr.psrs (0, CPSR)).F = F)
    /\
     ((si.machine1.psrs (0, CPSR)).F = F)
    /\
     ((si.machine2.psrs (0, CPSR)).F = F)
    /\
    ((sr.psrs (0, CPSR)).I = 
	((si.machine1.psrs (0, CPSR)).I ))
    /\
    ((sr.psrs (0, CPSR)).I = 
	((si.machine2.psrs (0, CPSR)).I ))
`;


(* determine if it's data abort or prefetch abort *)
val vector_table_address_def =    
    Define ` vector_table_address (ExcVectorBase:bool[32]) (mode:bool[5]) = 
if (mode = 17w:bool[5])
then
    [ExcVectorBase + 28w]
else if (mode = 18w:bool[5]) 
then  
    [ExcVectorBase + 24w]
else if (mode = 19w:bool[5]) 
then
    [ExcVectorBase + 8w]
else if (mode = 23w:bool[5]) 
then [ExcVectorBase + 16w; ExcVectorBase + 12w]
else (*if (mode = 27w)*) 
    [ExcVectorBase + 4w]
			`;


val get_security_ext_def = 
    Define `get_security_ext s = 
			     (((ARMarch2num s.information.arch = 5) ∨
                           (ARMarch2num s.information.arch = 7)) ∧
                          Extension_Security ∈ s.information.extensions)`;


val get_pc_value_def = 
Define `get_pc_value s1 = 
let is = (if (s1.psrs (0,CPSR)).J then
	  2 + if (s1.psrs (0,CPSR)).T then 1 else 0
      else if (s1.psrs (0,CPSR)).T then
	  1
      else
	  0) in
(if InstrSet2num (if is MOD 4 =
     0
 then
     InstrSet_ARM
 else if is MOD 4 =
	 1
     then
	 InstrSet_Thumb
     else if is MOD 4 =
	     2
	 then
	     InstrSet_Jazelle
	 else if is MOD 4 =
		 3
	     then
		 InstrSet_ThumbEE
	     else
			 ARB) =
    0
 then
     s1.registers (0,RName_PC) + 8w
 else
     (s1.registers (0,RName_PC) + 4w))`;


val get_base_vector_table_def =
    Define `get_base_vector_table y =
    if (y.coprocessors.state.cp15.SCTLR.V) 
    then
	0xFFFF0000w
    else
	if
	    (((ARMarch2num y.information.arch = 5) 
		  ∨
		  (ARMarch2num y.information.arch = 7)) 
		 ∧
		 Extension_Security ∈ y.information.extensions)
	then
	    (if
	 (¬y.coprocessors.state.cp15.SCR.NS 
		      ∨
         ((y.psrs (0,CPSR)).M = 22w))
	     then
		 y.coprocessors.state.cp15.VBAR.secure
	     else
		 y.coprocessors.state.cp15.VBAR.non_secure)
	else
	    0w:word32`;

val get_spsr_by_mode_def = 
    Define `get_spsr_by_mode (mode:bool[5]) = 
	case (mode) of
	         17w -> SPSR_fiq
	     || 18w -> SPSR_irq
	     || 19w -> SPSR_svc
	     || 22w -> SPSR_mon
	     || 23w -> SPSR_abt
	     || 27w -> SPSR_und`
;

val get_lr_by_mode_def = 
    Define `get_lr_by_mode (mode:bool[5]) = 
	case (mode) of
                17w -> RName_LRfiq
	     || 18w -> RName_LRirq
	     || 19w -> RName_LRsvc
	     || 22w -> RName_LRmon
	     || 23w -> RName_LRabt
	     || 27w -> RName_LRund
             ||  _  -> RName_LRusr `;


(* only for arm_next: no svc constraints *)
val priv_mode_constraints_v1_def = 
    Define `priv_mode_constraints_v1 (g:bool[32]) (state0:arm_state) state1 =
(state1.coprocessors.state.cp15 =
 state0.coprocessors.state.cp15)	

/\
(state1.information =
 state0.information)	

/\
((state1.psrs (0, CPSR)).F =
 (state0.psrs (0, CPSR)).F)

/\
((ARM_MODE state0 <> 16w) ==>
(ARM_MODE state1 <> 16w))

/\
((ARM_MODE state1 <> 16w) ==>
(ARM_MODE state0 = 16w))

/\
((ARM_MODE state1 = 16w) ==>
((state1.psrs (0, CPSR)).I = 
 (state0.psrs (0, CPSR)).I))

/\ 
((ARM_MODE state1 <> 16w) ==>
 (let spsr = get_spsr_by_mode (ARM_MODE state1)
 in
 ((state1.psrs (0, CPSR)).I = T)

/\
   ((state1.psrs (0, CPSR)).J = F)

/\
   ((state1.psrs (0, CPSR)).IT = 0w)

/\
   ((state1.psrs (0, CPSR)).E = 
    (state0.coprocessors.state.cp15.SCTLR.EE))

/\
~ (ARM_MODE state1 = 22w)

/\
~ (ARM_MODE state1 = 17w)

/\
~ (ARM_MODE state1 = 31w)

/\
(* program point to the handler of exception/interrupt in the vector table*)
((state1.registers (0, RName_PC) = 
	     (HD (vector_table_address (get_base_vector_table state0)
				  ((state1.psrs (0, CPSR)).M))))
\/
(state1.registers (0, RName_PC) = 
	     (HD (TL (vector_table_address (get_base_vector_table state0)
				  ((state1.psrs (0, CPSR)).M))))))

/\
(* in non-abort modes, we have no access violations *)
((* (ARM_MODE state1 <> 23w) ==>  *)
~(access_violation state1)) /\
((state1.psrs(0,spsr)).M = 16w) /\
((state1.psrs(0,spsr)).I = (state0.psrs(0,CPSR)).I)
 /\
((state1.psrs(0,spsr)).F = (state0.psrs(0,CPSR)).F)))
`;


(* only for arm_next : svc based on pc of previous state *)
val priv_mode_constraints_v2_def = 
    Define `priv_mode_constraints_v2 (g:bool[32]) (state0:arm_state) state1 =
priv_mode_constraints_v1 g state0 state1
/\
(* in svc mode, the link register is equal to old PC minus offset *)
((ARM_MODE state1 = 19w) ==>
              		 ((state1.registers (0, RName_LRsvc) =
			  (if (state0.psrs (0,CPSR)).T 
			   then
			       get_pc_value(state0) -2w
			   else
			       get_pc_value(state0) -4w			 
			  ))
                         /\ ((state1.psrs(0,SPSR_svc)) = (state0.psrs(0,CPSR)))))
`;

(* svc based on the borders *)
val priv_mode_constraints_v3_def = 
Define `priv_mode_constraints_v3 (g:bool[32]) (state0:arm_state) state1 =
    priv_mode_constraints_v2 g state0 state1
/\  ((ARM_MODE state1 = 19w) ==>
     (
       ((g = guest1) ==>
            ((((state1.psrs (0,SPSR_svc)).T) ==> (((state1.registers (0, RName_LRsvc) -2w) >=+ guest1_min_adr) /\ ((state1.registers (0, RName_LRsvc) -2w) <=+ guest1_max_adr))) 
       /\   ((((state1.psrs (0,SPSR_svc)).T = F) /\ ((state1.psrs (0,SPSR_svc)).J = F)) ==> (((state1.registers (0, RName_LRsvc) -4w) >=+ guest1_min_adr) /\ ((state1.registers (0, RName_LRsvc) -4w) <=+ guest1_max_adr))))) 
     /\
       ((g = guest2) ==>
            ((((state1.psrs (0,SPSR_svc)).T) ==> (((state1.registers (0, RName_LRsvc) -2w) >=+ guest2_min_adr) /\ ((state1.registers (0, RName_LRsvc) -2w) <=+ guest2_max_adr))) 
       /\   ((((state1.psrs (0,SPSR_svc)).T = F) /\ ((state1.psrs (0,SPSR_svc)).J = F)) ==> (((state1.registers (0, RName_LRsvc) -4w) >=+ guest2_min_adr) /\ ((state1.registers (0, RName_LRsvc) -4w) <=+ guest2_max_adr))))) 
     ))`;


(* svc based on accessible bytes *)
val priv_mode_constraints_v4_def = 
    Define `priv_mode_constraints_v4 (g:bool[32]) (state0:arm_state) state1 =			   
    priv_mode_constraints_v2 g state0 state1
/\  ((ARM_MODE state1 = 19w) ==>
     (
            (((state1.psrs (0,SPSR_svc)).T) ==> aligned_word_readable state1 T (state1.registers (0, RName_LRsvc) -2w)) 
       /\   ((((state1.psrs (0,SPSR_svc)).T = F) /\ ((state1.psrs (0,SPSR_svc)).J = F)) ==> aligned_word_readable state1 F (state1.registers (0, RName_LRsvc) -4w)) 
     ))`;


(* stack pointer of super mode is not touched in switching mode *)
val stack_pointer_constraint_def = 
     Define `stack_pointer_constraint  state1 =
         let mode = ARM_MODE state1 in
         let sp_reg = case mode of
                17w -> (RName_SPfiq)
             || 18w -> (RName_SPirq)
             || 19w -> (RName_SPsvc)
             || 22w -> (RName_SPmon)
             || 23w -> (RName_SPabt)
             || 27w -> (RName_SPund)
    in
	(state1.registers(0,sp_reg) >=0w) 
	   `;

(* only for arm_next *)
val priv_mode_similar_def = 
    Define `priv_mode_similar  (g:bool[32]) state1 state2 =
    (ARM_MODE state2 <> 16w) ==>
    (let mode = ARM_MODE state2
    in
	(state1.registers(0,get_lr_by_mode(mode)) = state2.registers(0,get_lr_by_mode(mode))) 
		/\ 
         (state1.psrs(0,get_spsr_by_mode(mode)) = state2.psrs(0,get_spsr_by_mode(mode))))	 
	`;

val inactive_guest_switched_mode_intrpt_flags_def = 
    Define `inactive_guest_switched_mode_intrpt_flags si g  =
	let inactive_machine = 
	    if g=guest1 then si.machine2
	    else
		si.machine1 
	in
	    ((inactive_machine.psrs (0, CPSR)).F = F)
(*	 /\ ((inactive_machine.psrs (0, CPSR)).I = F)*)
		`;


val coprocessor_constrains_def = 
    Define `coprocessor_constrains sr si g =
	    let active_machine = 
		if (g=guest1) 
		then si.machine1
		else
		    si.machine2
	    in
  ~(sr.coprocessors.state.cp15.SCTLR.EE) /\
  ~(si.machine1.coprocessors.state.cp15.SCTLR.EE) /\
  ~(si.machine2.coprocessors.state.cp15.SCTLR.EE) /\
  ~(sr.coprocessors.state.cp15.SCTLR.V) /\
  ~(si.machine1.coprocessors.state.cp15.SCTLR.V) /\
  ~(si.machine2.coprocessors.state.cp15.SCTLR.V) /\ 
   (sr.coprocessors.state.cp15.C1 = 
    active_machine.coprocessors.state.cp15.C1) /\
   (sr.coprocessors.state.cp15.C2 = 
    active_machine.coprocessors.state.cp15.C2) /\
   (sr.coprocessors.state.cp15.C3 = 
    active_machine.coprocessors.state.cp15.C3) /\
   (sr.coprocessors.state.cp14 = 
    si.machine1.coprocessors.state.cp14) /\
   (sr.coprocessors.state.cp14 = 
    si.machine2.coprocessors.state.cp14) /\
   (sr.coprocessors.state.cp15.SCTLR =
    si.machine1.coprocessors.state.cp15.SCTLR) /\
   (sr.coprocessors.state.cp15.SCTLR =
    si.machine2.coprocessors.state.cp15.SCTLR) /\
   (sr.coprocessors.state.cp15.SCR =
    si.machine1.coprocessors.state.cp15.SCR) /\
   (sr.coprocessors.state.cp15.SCR =
    si.machine2.coprocessors.state.cp15.SCR) /\
  (sr.coprocessors.state.cp15.NSACR =
    si.machine1.coprocessors.state.cp15.NSACR) /\
   (sr.coprocessors.state.cp15.NSACR =
    si.machine2.coprocessors.state.cp15.NSACR) /\
  (sr.coprocessors.state.cp15.VBAR =
    si.machine1.coprocessors.state.cp15.VBAR) /\
   (sr.coprocessors.state.cp15.VBAR =
    si.machine2.coprocessors.state.cp15.VBAR) /\
   (sr.coprocessors.state.cp15.MVBAR =
    si.machine1.coprocessors.state.cp15.MVBAR) /\
   (sr.coprocessors.state.cp15.MVBAR =
    si.machine2.coprocessors.state.cp15.MVBAR)

   `;


 (* g is active *)
val correct_user_mode_states_def = Define `correct_user_mode_states sr si g =
   let (other_guest) = 
       if g=guest1 then guest2 
       else 
	  guest1 in   
   (ARM_MODE sr = 16w)  /\
   (ARM_MODE si.machine1 = 16w) /\
   (ARM_MODE si.machine2 = 16w) /\
   (si.logical_component.context1.spsr.M = 16w) /\
   (si.logical_component.context2.spsr.M = 16w) /\
   (guests_equal_memory sr si) /\ 
   (active_guest_equal_regs_psrs sr si g ) /\
   (inactive_guest_equal_regs_psrs sr si other_guest ) /\
   (hypervisor_constraints sr si g ) /\
   (user_mode_constraints sr si g) /\
   (coprocessor_constrains sr si g) /\
   (    ((guest_context_adr g sr.memory) = (g + o_virtual_machine__mode_states + t_hyper_mode_state_len))
     \/ ((guest_context_adr g sr.memory) = (g + o_virtual_machine__mode_states))) /\
   (    ((guest_context_adr other_guest sr.memory) = (other_guest + o_virtual_machine__mode_states + t_hyper_mode_state_len))
     \/ ((guest_context_adr other_guest sr.memory) = (other_guest + o_virtual_machine__mode_states)))
(*
   (kth_hyp_vm_invariants sr global_vm_0_add global_vm_1_add
			  global_minimal_config_add
                          global_gm_interrupt_1_add
   ) /\
   (kth_hyp_vm_invariants sr global_vm_1_add global_vm_0_add
			  (global_minimal_config_add +
			   t_hc_config_len)
			  global_gm_interrupt_2_add
   )
*)
/\
     (if (g=guest1) 
      then
	  access_violation sr = access_violation si.machine1
      else
	  access_violation sr = access_violation si.machine2) 
`;

val gen_untouched_def = Define ` gen_untouched sr' si' sr si g =
    let (active,inactive,
	 old_active,old_inactive) =
	if (g=guest1)
	then
	    (si.machine1,si.machine2,
	     si'.machine1,si'.machine2)
	else
	    (si.machine2,si.machine1,
	     si'.machine2,si'.machine1)
    in
	(untouched g sr' sr) /\
	(untouched g old_active active) /\
	(inactive = old_inactive) /\
        (si.logical_component = si'.logical_component)
    `;

(* User Lemma *)
val user_mode_thm = new_axiom 
("user_mode_thm", `` 
    ! sr si  ra cycle ta rnext rc g .
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
                (gen_untouched sr si rnext inext g)))))
 ``);


val user_mode_error_thm = 
new_axiom 
("user_mode_error_thm", `` 
   ! sr si cycle g er rc .
    (((g=guest1) \/ (g=guest2)) /\ 
     (correct_user_mode_states sr si g ) /\
     (mmu_requirements sr g)    /\
     (mmu_requirements si.machine1 guest1)  /\
     (mmu_requirements si.machine2 guest2)  /\ 
     (ARM_MODE sr = 0b10000w)    /\
     (one_step_real sr cycle  <|proc:=0|>  = (Error er ,rc))
   )
   ==>
    (? ei ic mode'.( one_step_ideal si cycle  <|proc:=0|> = (Error ei,ic,mode')) /\ (er=ei))
         ``);

(* g is active *)
val correct_switched_mode_states_def = Define ` correct_switched_mode_states sr si sr0 si0  g  =
   let (other_guest) = 
       if (g=guest1) then 
	   guest2 
       else 
	   guest1 in   
   let active_machine = 
       if (g=guest1) then 
	   si.machine1 
       else 
	   si.machine2 in   
   let old_active_machine =
       if (g=guest1) then
   	   si0.machine1
       else
   	   si0.machine2 in
   let mode = ARM_MODE sr in
   (
    if (g = guest1 ) then 
       ((ARM_MODE sr = ARM_MODE si.machine1) /\ 
        (ARM_MODE si.machine2 = 16w))
    else
       ((ARM_MODE sr = ARM_MODE si.machine2)  /\ 
        (ARM_MODE si.machine1 = 16w)) 
   ) 
   /\
   (guests_equal_memory sr si) /\ 
   (active_guest_equal_regs_psrs sr si g ) /\
   (inactive_guest_equal_regs_psrs sr si other_guest ) /\
   (hypervisor_constraints sr si g  ) /\
   (coprocessor_constrains sr si g) /\
   (priv_mode_constraints_v3  g sr0 sr) /\
   (priv_mode_constraints_v3  g old_active_machine active_machine)/\ 
   (priv_mode_similar  g sr active_machine) /\
   (* (stack_pointer_constraint  sr ) /\ *)
   (inactive_guest_switched_mode_intrpt_flags si g )
 `;


val switched_mode_thm = 
    new_axiom ("switched_mode_thm", `` 
    !  rs is rs' cycle ra rc g .
    (((g=guest1) \/ (g=guest2)) /\ 
     (correct_user_mode_states rs is g ) /\
     (mmu_requirements rs g)    /\
     (mmu_requirements is.machine1 guest1)  /\
     (mmu_requirements is.machine2 guest2)  /\ 
     (ARM_MODE rs = 0b10000w)    /\
     (one_step_real rs cycle <|proc:=0|> = (ValueState ra rs',rc)))
   ==>
    (? im ia is' .
    (one_step_ideal is cycle <|proc:=0|> = (ValueState ia is',rc,im)) /\
    (im = ARM_MODE rs') /\ ((im <> 0b10000w) ==>
       ((correct_switched_mode_states rs' is' rs is g ) /\
                (gen_untouched rs is rs' is' g))))
 ``);

