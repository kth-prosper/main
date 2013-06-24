no_changed_memory:bool = (
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
      (free_addr:u32 < ($global_context_stack_add+4:u32+4:u32)) &
      (free_addr:u32 >= ($global_context_stack_add+4:u32))
  ) |
  (
      (free_addr:u32 < ($global_curr_vm_add+4:u32)) &
      (free_addr:u32 >= ($global_curr_vm_add))
  ) |
  (
      (free_addr:u32 < (0xfffff130:u32+4:u32)) &
      (free_addr:u32 >= (0xfffff130:u32))
  ) |
  (
      (free_addr:u32 < (0xfffff124:u32+4:u32)) &
      (free_addr:u32 >= (0xfffff124:u32))
  ) |
  (
      (free_addr:u32 < (0xfffff120:u32+4:u32)) &
      (free_addr:u32 >= (0xfffff120:u32))
  ) |
  (
      (free_addr:u32 < (old_SP_SVC:u32 -4:u32+4:u32)) &
      (free_addr:u32 >= (old_SP_SVC:u32 -16:u32))
  ) |
  old_mem[free_addr:u32,e_little]:u8 == mem[free_addr:u32,e_little]:u8
)

changed_registers:bool = (
   (
      let tmp_ctx_ptr:u32 := if (old_vm0_active) then
      	  		     	old_vm1_curr_mode_ptr else
				old_vm0_curr_mode_ptr
      in (
      	 (old_mem[tmp_ctx_ptr+4:u32 *0:u32, e_little]:u32 == R0) &
      	 (old_mem[tmp_ctx_ptr+4:u32 *1:u32, e_little]:u32 == R1) &
      	 (old_mem[tmp_ctx_ptr+4:u32 *2:u32, e_little]:u32 == R2) &
      	 (old_mem[tmp_ctx_ptr+4:u32 *3:u32, e_little]:u32 == R3) &
      	 (old_mem[tmp_ctx_ptr+4:u32 *4:u32, e_little]:u32 == R4) &
      	 (old_mem[tmp_ctx_ptr+4:u32 *5:u32, e_little]:u32 == R5) &
      	 (old_mem[tmp_ctx_ptr+4:u32 *6:u32, e_little]:u32 == R6) &
      	 (old_mem[tmp_ctx_ptr+4:u32 *7:u32, e_little]:u32 == R7) &
      	 (old_mem[tmp_ctx_ptr+4:u32 *8:u32, e_little]:u32 == R8) &
      	 (old_mem[tmp_ctx_ptr+4:u32 *9:u32, e_little]:u32 == R9) &
      	 (old_mem[tmp_ctx_ptr+4:u32 *10:u32, e_little]:u32 == R10) &
      	 (old_mem[tmp_ctx_ptr+4:u32 *11:u32, e_little]:u32 == R11) &
      	 (old_mem[tmp_ctx_ptr+4:u32 *12:u32, e_little]:u32 == R12) &
      	 (old_mem[tmp_ctx_ptr+4:u32 *13:u32, e_little]:u32 == SP) &
      	 (old_mem[tmp_ctx_ptr+4:u32 *14:u32, e_little]:u32 == LR) &
      	 (old_mem[tmp_ctx_ptr+4:u32 *15:u32, e_little]:u32 == PC) &
	 true
    ))
)

new_invariant:bool = 
  (SP_SVC:u32 <= (0x100000:u32 - 4:u32)) &
  (SP_SVC:u32 >= 0x0f0000:u32)

changed_flags:bool = (
      let tmp_ctx_ptr:u32 := if (old_vm0_active) then
      	  		     	old_vm1_curr_mode_ptr else
				old_vm0_curr_mode_ptr in
      let old_psr_value:u32 := old_mem[tmp_ctx_ptr+$o_context:psr, e_little]:u32 in
      (
        N_FLAG == low:bool(old_psr_value >> 31:u32) &
        Z_FLAG == low:bool(old_psr_value >> 30:u32) &
        C_FLAG == low:bool(old_psr_value >> 29:u32) &
        V_FLAG == low:bool(old_psr_value >> 28:u32) &
        Q_FLAG == low:bool(old_psr_value >> 27:u32)
      )
)

changed_cp:bool = 
    (
	(old_vm0_active & (CR3 == 0x11:u32)) |
	(old_vm1_active & (CR3 == 0x5:u32))
    ) & (CR0 == 0x0:u32)

changed_memory:bool = (
  let new_vm:u32 := mem[$global_curr_vm_add, e_little]:u32 in (
    (
     (old_vm0_active & (new_vm == $global_vm_1_add)) |
     (old_vm1_active & (new_vm == $global_vm_0_add))
    ) &
    (
      let new_context_stack_ptr:u32 := mem[$global_context_stack_add+4:u32, e_little]:u32 in (
       (old_vm0_active & (
         new_context_stack_ptr == old_vm1_curr_mode_ptr
       )) |
       (old_vm1_active & (
         new_context_stack_ptr == old_vm0_curr_mode_ptr
       ))
    )) &
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
      	 (mem[tmp_ctx_ptr+4:u32 *13:u32, e_little]:u32 == old_SP) &
      	 (mem[tmp_ctx_ptr+4:u32 *14:u32, e_little]:u32 == old_LR) &
      	 (mem[tmp_ctx_ptr+4:u32 *15:u32, e_little]:u32 == old_LR_SVC-4:u32) &
	 ( let tmp_saved_psr_value:u32 := mem[tmp_ctx_ptr+$o_context:psr, e_little]:u32 in
            (
              old_SVC_N_FLAG == low:bool(tmp_saved_psr_value >> 31:u32) &
              old_SVC_Z_FLAG == low:bool(tmp_saved_psr_value >> 30:u32) &
              old_SVC_C_FLAG == low:bool(tmp_saved_psr_value >> 29:u32) &
              old_SVC_V_FLAG == low:bool(tmp_saved_psr_value >> 28:u32) &
              old_SVC_Q_FLAG == low:bool(tmp_saved_psr_value >> 27:u32)
            )
	 )
    ))
))


postcondition:bool = new_invariant & changed_registers & changed_flags & changed_cp & changed_memory & no_changed_memory
// postcondition:bool = no_changed_memory