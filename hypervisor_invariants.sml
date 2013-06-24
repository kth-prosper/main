
(*
Problem to verify exp3 in sd_supports_MMU: sbz is 1
Problem to verify exp4 in sd_supports_MMU
*)
val mmu_boot_setup_sdi_def = Define `
 mmu_boot_setup_sdi state sdi = 
 let first_sd = global_flpt_add && (0xFFFFC000w:bool[32]) in 
    let adr_sd =  first_sd + 4w * sdi in
    let content_of_sd = read_mem32 adr_sd state.memory in
    let domain:bool[32] = (content_of_sd && 0x000001E0w:bool[32]) >>> 5 in
    let AP = (content_of_sd && 0x00000C00w) >>> 10 in
    let sdi_log_add = sdi << 20 in
	(sd_supports_MMU content_of_sd sdi) /\
	((sdi_log_add >=+ guest1_min_adr /\
          sdi_log_add <=+ guest1_max_adr) ==> (AP = 0b11w) /\ (domain = 1w))
	/\
	((sdi_log_add >=+ guest2_min_adr /\
          sdi_log_add <=+ guest2_max_adr) ==> (AP = 0b11w) /\ (domain = 2w))
        /\
	((~(sdi_log_add >=+ guest1_min_adr /\
          sdi_log_add <=+ guest1_max_adr) /\
	  ~(sdi_log_add >=+ guest2_min_adr /\
           sdi_log_add <=+ guest2_max_adr)) 
	  ==> (AP = 0b01w) /\ (domain = 0w))
`;

val mmu_boot_setup_sdi_inv_def = Define `
 mmu_boot_setup_sdi_inv state max_sdi = 
 !sdi.  (sdi>=+ 0w:bool[32] /\ sdi <+ 4096w:bool[32] /\ sdi <+ max_sdi) ==>
	mmu_boot_setup_sdi state sdi
`;

val mmu_boot_setup_def = Define `
 mmu_boot_setup state = 
 !sdi.  (sdi>=+ 0w:bool[32] /\ sdi <+ 4096w:bool[32]) ==>
	mmu_boot_setup_sdi state sdi
`;


val mmu_coprocessor_setup_def = Define `
  mmu_coprocessor_setup state guest =
   (state.coprocessors.state.cp15.C2 = global_flpt_add) /\
   (state.coprocessors.state.cp15.C1 = 1w)  /\
   if (guest = guest1) then
       state.coprocessors.state.cp15.C3 = 0b000101w
   else if (guest = guest2) then
       state.coprocessors.state.cp15.C3 = 0b010001w
   else
       F
`;

(**************************************)
(*           KTH invariants           *)
(**************************************)
val read_c_field_word_def = 
    Define `read_c_field_word address (offset:bool[32]) memory =
	read_mem32 (address+offset) memory
`;
 
val kth_hyp_vm_invariants_def = 
    Define `kth_hyp_vm_invariants s vm_add other_vm_add conf_add 
       interrupt_add
       =
(* The virtual machien list is a cyrcular linked list *)
        ((read_c_field_word vm_add o_virtual_machine__next s.memory) = other_vm_add) /\
(* The pointer to the current mode must be consistent, pointing to one of the two array modes *)
    (
        ((read_c_field_word vm_add o_virtual_machine__current_mode_state s.memory) = 
	 vm_add + o_virtual_machine__mode_states) \/
        ((read_c_field_word vm_add o_virtual_machine__current_mode_state s.memory) = 
	 vm_add + o_virtual_machine__mode_states + t_hyper_mode_state_len)
    ) /\
(* The configuration field is a constant *)
        ((read_c_field_word vm_add o_virtual_machine__config s.memory)
    = conf_add) /\
(* current guest mode is consistend with the pointer
    current_mode_state*)
   (
        ((read_c_field_word vm_add o_virtual_machine__current_mode_state s.memory) = 
	 vm_add + o_virtual_machine__mode_states + 
	 (read_c_field_word vm_add
			    o_virtual_machine__current_guest_mode s.memory) *
	 t_hyper_mode_state_len)
   ) /\
(* The modes point to the right configuration *)
   (
    let mode1_add = vm_add + o_virtual_machine__mode_states in
    let mode2_add = vm_add + o_virtual_machine__mode_states +
    t_hyper_mode_state_len in
  (
    ((read_c_field_word mode1_add o_hyper_mode_state__mode_config
    s.memory) = interrupt_add) /\
    ((read_c_field_word mode2_add o_hyper_mode_state__mode_config
    s.memory) = (interrupt_add + t_hc_guest_mode_len)))
   ) /\
(* We have only two modes for the guests*)
(
  ((read_c_field_word vm_add o_virtual_machine__current_guest_mode
    s.memory) = 0w) \/
  ((read_c_field_word vm_add o_virtual_machine__current_guest_mode
    s.memory) = 1w)
)
`;


val kth_board_invariants_def = 
    Define `kth_board_invariants s =
  (
     (read_mem32 (0xfffff100w) s.memory = f_irq_handler_add) /\
     (read_mem32 (global_family_callback_swi_add) s.memory =
    f_swi_handler_add) /\
     (read_mem32 (global_family_callback_data_abort_add) s.memory =
    f_data_abort_handler_add) /\
     (read_mem32 (global_family_callback_undef_add) s.memory =
    f_undef_handler_add) /\
     (read_mem32 (global___bss_start___add) s.memory =
    f_prog_abort_handler_add)
     
  )
`;
	    
val kth_config_invariants_def = 
    Define `kth_config_invariants s =
(* Confifuration states that the mode to activate upon recerion of messages has index 0 for both vm *)
  (
     (read_mem32 (global_minimal_config_add+o_hc_config__interrupt_config+o_hc_interrupt_config__interrupt_mode) s.memory = 0w) /\
     (read_mem32 (global_minimal_config_add+t_hc_config_len+o_hc_config__interrupt_config+o_hc_interrupt_config__interrupt_mode) s.memory = 0w)
  ) /\
(* Domain masks of the four static modes *)
  (
     (read_c_field_word global_gm_interrupt_1_add o_hc_guest_mode__domain_ac s.memory = 0x5w) /\
     (read_c_field_word global_gm_task_1_add o_hc_guest_mode__domain_ac s.memory = 0x5w) /\
     (read_c_field_word global_gm_interrupt_2_add o_hc_guest_mode__domain_ac s.memory = 0x11w) /\
     (read_c_field_word global_gm_task_2_add o_hc_guest_mode__domain_ac s.memory = 0x11w) 
  )
`;

val kth_vms_invariants_def = 
    Define `kth_vms_invariants s =
    let vm0_active = (read_mem32 global_curr_vm_add s.memory = global_vm_0_add) in
    let vm1_active = (read_mem32 global_curr_vm_add s.memory = global_vm_1_add) in
(* The current virtual machine must point to one of the two existing guests *)
    (
	vm0_active \/ vm1_active
    ) /\
(* Invariants for the structures of the two virtual machines *)
   (
        (kth_hyp_vm_invariants s global_vm_0_add global_vm_1_add
    global_minimal_config_add global_gm_interrupt_1_add) /\
        (kth_hyp_vm_invariants s global_vm_1_add global_vm_0_add
    (global_minimal_config_add + t_hc_config_len) global_gm_interrupt_2_add) 
   ) /\
(* Context stack: in our simplified settings this cointains always one entry *)
   (
        (read_mem32 global_context_stack_curr_add s.memory = 0w) /\
        (
	  (vm0_active) ==>
	  (read_mem32 (global_context_stack_add + 4w) s.memory =
	   (read_c_field_word global_vm_0_add o_virtual_machine__current_mode_state s.memory)
	  )
	) /\
        (
	  (vm1_active) ==>
	  (read_mem32 (global_context_stack_add + 4w) s.memory =
	   (read_c_field_word global_vm_1_add o_virtual_machine__current_mode_state s.memory)
	  )
	)
   )
`;

val kth_hyp_invariants_def = 
    Define `kth_hyp_invariants s =
    (kth_board_invariants s) /\
    (kth_config_invariants s) /\
    (kth_vms_invariants s)
`;
