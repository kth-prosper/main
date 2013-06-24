new_invariant:bool = 
  (
  (SP_SVC:u32 <= (0x100000:u32 - 4:u32)) &
  (SP_SVC:u32 >= 0x0f0000:u32))
  | SP_SVC:u32 <> free_var_new_inv:u32

changed_cp:bool = 
    (
	(old_vm0_active & (CR3 == 0x11:u32)) |
	(old_vm1_active & (CR3 == 0x5:u32))
    ) & (CR0 == 0x0:u32)


changed_registers:bool = (
   (
      let tmp_ctx_ptr:u32 := if (old_vm0_active) then
      	  		     	vm1_mode1_add else
				vm0_mode1_add in
      (
      // let tmp_sp_add:u32 := if (old_vm1_active) then
      // 	  		     	(minimal_config_2_mode1_sp) else
      // 				(minimal_config_1_mode1_sp) in
      // let tmp_pc_add:u32 := if (old_vm1_active) then
      // 	  		     	(minimal_config_2_mode1_pc) else
      // 				(minimal_config_1_mode1_pc) in
	 (old_vm1_active | (old_mem[$global_vm_1_add + $o_virtual_machine:message, e_little]:u32 == R0)) &
	 (old_vm0_active | (old_mem[$global_vm_0_add + $o_virtual_machine:message, e_little]:u32 == R0)) &
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
      	 (old_mem[tmp_ctx_ptr+4:u32 *14:u32, e_little]:u32 == LR) &
	 true
    ))
)

// Error in psr
changed_flags:bool = (
      let tmp_ctx_ptr:u32 := if (old_vm0_active) then
      	  		     	vm1_mode1_add else
				vm0_mode1_add in
      let old_psr_value:u32 := old_mem[tmp_ctx_ptr+$o_context:psr, e_little]:u32 in
      (
        N_FLAG == low:bool(old_psr_value >> 31:u32) &
        Z_FLAG == low:bool(old_psr_value >> 30:u32) &
        C_FLAG == low:bool(old_psr_value >> 29:u32) &
        V_FLAG == low:bool(old_psr_value >> 28:u32) &
        Q_FLAG == low:bool(old_psr_value >> 27:u32)
      )
)

postcondition:bool = new_invariant & changed_cp
postcondition:bool = changed_registers
