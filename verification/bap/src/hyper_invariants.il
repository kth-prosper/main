inv_memory_curr_vm:bool = (
	(old_vm0_active:bool == (mem[$global_curr_vm_add, e_little]:u32 ==$global_vm_0_add)) &
	(old_vm1_active:bool == (mem[$global_curr_vm_add, e_little]:u32 ==$global_vm_1_add)) &
	(old_vm0_active:bool | old_vm1_active:bool) 
)

inv_struct_modes:bool = (
  (old_mem[$global_gm_interrupt_1_add+($o_hc_guest_mode:domain_ac), e_little]:u32 == 2:u32) &
  (old_mem[$global_gm_task_1_add+($o_hc_guest_mode:domain_ac), e_little]:u32 == 2:u32) &
  (old_mem[$global_gm_interrupt_2_add+($o_hc_guest_mode:domain_ac), e_little]:u32 == 4:u32) &
  (old_mem[$global_gm_task_2_add+($o_hc_guest_mode:domain_ac), e_little]:u32 == 4:u32)
)

inv_struct_vm0:bool = (
	(vm0_mode1_add:u32 ==  $global_vm_0_add + ($o_virtual_machine:mode_states)) &
	(vm0_mode2_add:u32 ==  $global_vm_0_add + ($o_virtual_machine:mode_states) + (1:u32 * $t_hyper_mode_state_len)) &
	(vm0_next:u32 == mem[$global_vm_0_add + $o_virtual_machine:next, e_little]:u32) &
	(vm0_next == $global_vm_1_add) &
	(old_vm0_curr_mode_ptr:u32 == mem[$global_vm_0_add + $o_virtual_machine:current_mode_state, e_little]:u32) &
        (
	    (old_vm0_curr_mode_ptr == vm0_mode1_add) |
	    (old_vm0_curr_mode_ptr == vm0_mode2_add)
	) &
	(
		mem[vm0_mode1_add+($o_hyper_mode_state:mode_config), e_little]:u32 == $global_gm_interrupt_1_add &
		mem[vm0_mode2_add+($o_hyper_mode_state:mode_config), e_little]:u32 == $global_gm_task_1_add
	) &
	(mem[$global_vm_0_add+$o_virtual_machine:config, e_little]:u32 == $global_minimal_config_add)
)

inv_struct_vm1:bool = (
	(vm1_mode1_add:u32 ==  $global_vm_1_add + ($o_virtual_machine:mode_states)) &
	(vm1_mode2_add:u32 ==  $global_vm_1_add + ($o_virtual_machine:mode_states) + (1:u32 * $t_hyper_mode_state_len)) &
	(vm1_next:u32 == mem[$global_vm_1_add + $o_virtual_machine:next, e_little]:u32) &
	(vm1_next == $global_vm_0_add) &
	(old_vm1_curr_mode_ptr:u32 == mem[$global_vm_1_add + $o_virtual_machine:current_mode_state, e_little]:u32) &
        (
	    (old_vm1_curr_mode_ptr == vm1_mode1_add) |
	    (old_vm1_curr_mode_ptr == vm1_mode2_add)
	) &
	(
		mem[vm1_mode1_add+($o_hyper_mode_state:mode_config), e_little]:u32 == $global_gm_interrupt_2_add &
		mem[vm1_mode2_add+($o_hyper_mode_state:mode_config), e_little]:u32 == $global_gm_task_2_add
	) &
	(mem[$global_vm_1_add+$o_virtual_machine:config, e_little]:u32 == $global_minimal_config_add + $t_hc_config_len)
)

inv_struct_vms:bool = inv_struct_vm0 & inv_struct_vm1;

inv_context_stack:bool =
  (old_curr_context_stack_index:u32 == old_mem[$global_context_stack_curr_add, e_little]:u32) &
  (old_curr_context_stack_index == 0:u32) &
  (old_context_stack_ptr:u32 == old_mem[$global_context_stack_add + 4:u32, e_little]:u32) &
    ((old_vm0_active & (
      old_context_stack_ptr  == old_vm0_curr_mode_ptr
    )) |
    (old_vm1_active & (
      old_context_stack_ptr  == old_vm1_curr_mode_ptr
    ))
  )


inv_others:bool = (
  (old_LR_SVC:u32 >= 0x10000000:u32) &
  (old_LR_SVC:u32 < 0x30000000:u32) &
  (old_SP_SVC:u32 <= (0x100000:u32 - 4:u32)) &
  (old_SP_SVC:u32 >= 0x0f0000:u32) &

  (old_mem[0xfffff100:u32, e_little]:u32 == $f_irq_handler_add) &
  (old_mem[$global_family_callback_swi_add, e_little]:u32 == $f_swi_handler_add) &
  
  (old_mem[$global_minimal_config_add+$o_hc_config:interrupt_config+$o_hc_interrupt_config:interrupt_mode, e_little]:u32 == 0:u32) &
  (old_mem[$global_minimal_config_add+$t_hc_config_len+$o_hc_config:interrupt_config+$o_hc_interrupt_config:interrupt_mode, e_little]:u32 == 0:u32) &

  (old_mem[0x18234:u32, e_little]:u32 == 0x00100000:u32) & 
  (old_mem[0x18238:u32, e_little]:u32 == 0x002ffffc:u32) &
  (old_mem[0x1823c:u32, e_little]:u32 == 0x00000001:u32) &	 
  (old_mem[0x18280:u32, e_little]:u32 == 0x00001374:u32) &
  (old_mem[0x18284:u32, e_little]:u32 == 0x00001388:u32) &
  (old_mem[0x18288:u32, e_little]:u32 == 0x00000000:u32) &
  (old_mem[0x1828c:u32, e_little]:u32 == 0x003ffffc:u32) &
  (old_mem[0x18290:u32, e_little]:u32 == 0x00200000:u32) &
  (old_mem[0x182a0:u32, e_little]:u32 == 0x00400000:u32) &
  (old_mem[0x182a4:u32, e_little]:u32 == 0x005ffffc:u32) &
  (old_mem[0x182a8:u32, e_little]:u32 == 0x00000001:u32) &
  (old_mem[0x182ec:u32, e_little]:u32 == 0x0000139c:u32) &
  (old_mem[0x182f0:u32, e_little]:u32 == 0x000013b0:u32) &
  (old_mem[0x182f4:u32, e_little]:u32 == 0x00000000:u32) &
  (old_mem[0x182f8:u32, e_little]:u32 == 0x006ffffc:u32) &
  (old_mem[0x182fc:u32, e_little]:u32 == 0x00500000:u32) &

  (old_mem[$global_gm_interrupt_1_add + $o_hc_guest_mode:domain_ac, e_little]:u32 == 0x5:u32) &
  (old_mem[$global_gm_task_1_add + $o_hc_guest_mode:domain_ac, e_little]:u32 == 0x5:u32) &
  (old_mem[$global_gm_interrupt_2_add + $o_hc_guest_mode:domain_ac, e_little]:u32 == 0x11:u32) &
  (old_mem[$global_gm_task_2_add + $o_hc_guest_mode:domain_ac, e_little]:u32 == 0x11:u32) &

  true
)

hyper_invariants:bool = (
  inv_struct_vms &
  inv_memory_curr_vm &
  inv_context_stack &
  inv_others
)
