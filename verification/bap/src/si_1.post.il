no_change_memory:bool = (
  (
    (
	(old_vm0_active & (
	   free_addr:u32 >= old_vm0_curr_mode_ptr &
	   free_addr:u32 < old_vm0_curr_mode_ptr + $t_context_len
	)) |
	(old_vm1_active & (
	   free_addr:u32 >= old_vm1_curr_mode_ptr &
	   free_addr:u32 < old_vm1_curr_mode_ptr + $t_context_len
        ))
    ) |
    (
      (free_addr:u32 < (old_SP_SVC:u32 -4:u32+4:u32)) &
      (free_addr:u32 >= (old_SP_SVC:u32 -16:u32))
    )
  ) |
  (
    (old_vm1_active & (
      ((free_addr:u32 < ($global_vm_0_add+$o_virtual_machine:message+4:u32)) &
       (free_addr:u32 >= ($global_vm_0_add+$o_virtual_machine:message))) |
      ((free_addr:u32 < ($global_vm_0_add+$o_virtual_machine:b_new_message+4:u32)) &
       (free_addr:u32 >= ($global_vm_0_add+$o_virtual_machine:b_new_message)))
       )) |
    (old_vm0_active & (
      ((free_addr:u32 < ($global_vm_1_add+$o_virtual_machine:message+4:u32)) &
       (free_addr:u32 >= ($global_vm_1_add+$o_virtual_machine:message))) |
      ((free_addr:u32 < ($global_vm_1_add+$o_virtual_machine:b_new_message+4:u32)) &
       (free_addr:u32 >= ($global_vm_1_add+$o_virtual_machine:b_new_message)))
       ))
  ) |
  old_mem[free_addr:u32,e_little]:u8 == mem[free_addr:u32,e_little]:u8
)

changed_memory:bool = (
(
      let tmp_ctx_ptr:u32 := if (old_vm0_active) then
      	  		     	old_vm0_curr_mode_ptr else
				old_vm1_curr_mode_ptr
      in (
      	 (mem[tmp_ctx_ptr+4:u32 *0:u32, e_little]:u32 == old_R0) &
      	 (mem[tmp_ctx_ptr+4:u32 *1:u32, e_little]:u32 == old_R1) &
      	 (mem[tmp_ctx_ptr+4:u32 *2:u32, e_little]:u32 == old_R2) &
      	 (mem[tmp_ctx_ptr+4:u32 *3:u32, e_little]:u32 == old_R3) &
      	 (mem[tmp_ctx_ptr+4:u32 *4:u32, e_little]:u32 == old_R4) &
      	 (mem[tmp_ctx_ptr+4:u32 *5:u32, e_little]:u32 == old_R5) &
      	 (mem[tmp_ctx_ptr+4:u32 *6:u32, e_little]:u32 == old_R6) &
      	 (mem[tmp_ctx_ptr+4:u32 *7:u32, e_little]:u32 == old_R7) &
      	 (mem[tmp_ctx_ptr+4:u32 *8:u32, e_little]:u32 == old_R8) &
      	 (mem[tmp_ctx_ptr+4:u32 *9:u32, e_little]:u32 == old_R9) &
      	 (mem[tmp_ctx_ptr+4:u32 *10:u32, e_little]:u32 == old_R10) &
      	 (mem[tmp_ctx_ptr+4:u32 *11:u32, e_little]:u32 == old_R11) &
      	 (mem[tmp_ctx_ptr+4:u32 *12:u32, e_little]:u32 == old_R12) &
      	 (mem[tmp_ctx_ptr+4:u32 *13:u32, e_little]:u32 == old_SP)
    )) &
        (
  	  (old_vm0_active & (
	    mem[$global_vm_1_add+$o_virtual_machine:b_new_message, e_little]:u32 == 1:u32 &
	    mem[$global_vm_1_add+$o_virtual_machine:message, e_little]:u32 == old_R1
	  )) |
	  (old_vm1_active & (
  	    mem[$global_vm_0_add+$o_virtual_machine:b_new_message, e_little]:u32 == 1:u32 &
	    mem[$global_vm_0_add+$o_virtual_machine:message, e_little]:u32 == old_R1
	  ))
	)
);

no_change_registers:bool = 
	(old_R0:u32 == R0:u32) &
	(old_R1:u32 == R1:u32) &
	(old_R2:u32 == R2:u32) &
	(old_R3:u32 == R3:u32) &
	(old_R4:u32 == R4:u32) &
	(old_R5:u32 == R5:u32) &
	(old_R6:u32 == R6:u32) &
	(old_R7:u32 == R7:u32) &
	(old_R8:u32 == R8:u32) &
	(old_R9:u32 == R9:u32) &
	(old_R10:u32 == R10:u32) &
	(old_R11:u32 == R11:u32) &
	(old_R12:u32 == R12:u32) &
	(old_SP:u32 == SP:u32) &
	(old_LR:u32 == LR:u32) &
	(old_LR_SVC:u32 == LR_SVC:u32) &
	(old_LR_SVC:u32 == PC:u32) &
	true


new_invariant:bool = 
  (SP_SVC:u32 <= (0x100000:u32 - 4:u32)) &
  (SP_SVC:u32 >= 0x0f0000:u32)


no_changed_flags:bool = (
    old_SVC_N_FLAG:bool  == N_FLAG:bool &
    old_SVC_C_FLAG:bool  == C_FLAG:bool &
    old_SVC_Z_FLAG:bool  == Z_FLAG:bool &
    old_SVC_V_FLAG:bool  == V_FLAG:bool &
    old_SVC_Q_FLAG:bool  == Q_FLAG:bool
)

no_changed_cp:bool = 
   (CR3 == old_CR3)  & (CR0 == old_CR0)

postcondition:bool = no_change_registers & changed_memory & new_invariant & no_change_memory & no_changed_flags & no_changed_cp
//postcondition:bool = no_changed_cp