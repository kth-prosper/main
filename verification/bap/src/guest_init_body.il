#set start_pc=[[0xB08]]
#set last_pc=[[0xB44]]
#set print_add=[[0xE5C]]

#include "src/backup_state.il"
#include "../out/loc_symbols.il"
#include "../out/loc_code_memory.il"
#include "../out/types.il"



precondition:bool = (
  loc_code_memory &
  mem[$global_vm_0_add + $o_virtual_machine:next, e_little]:u32 == $global_vm_1_add &
  mem[$global_vm_1_add + $o_virtual_machine:next, e_little]:u32 == $global_vm_0_add &
  
  ((R0 == $global_vm_0_add &
    R2 == ($global_vm_0_add + ($o_virtual_machine:mode_states) + (1:u32 * $t_hyper_mode_state_len)) &
    mem[$global_vm_0_add + ($o_virtual_machine:mode_states)+($o_hyper_mode_state:mode_config), e_little]:u32 == $global_gm_interrupt_1_add &
    mem[$global_vm_0_add + ($o_virtual_machine:mode_states)+($o_hyper_mode_state:mode_config)  + (1:u32 * $t_hyper_mode_state_len), e_little]:u32 == $global_gm_task_1_add &
    mem[$global_vm_0_add+$o_virtual_machine:config, e_little]:u32 == $global_minimal_config_add &
    true)
  |
   (R0 == $global_vm_1_add &

// All the following are the postcondition of the first iteration
  mem[$global_vm_0_add + $o_virtual_machine:next, e_little]:u32 == $global_vm_1_add &
  mem[$global_vm_0_add + $o_virtual_machine:current_mode_state, e_little]:u32 == 
       ($global_vm_0_add + ($o_virtual_machine:mode_states) +
       (1:u32 * $t_hyper_mode_state_len)) &
  mem[$global_vm_0_add + ($o_virtual_machine:mode_states)+($o_hyper_mode_state:mode_config), e_little]:u32 == $global_gm_interrupt_1_add &
  mem[$global_vm_0_add + ($o_virtual_machine:mode_states)+($o_hyper_mode_state:mode_config)  + (1:u32 * $t_hyper_mode_state_len), e_little]:u32 == $global_gm_task_1_add &
  mem[$global_vm_0_add + $o_virtual_machine:current_guest_mode, e_little]:u32 == 1:u32 &
  mem[$global_vm_0_add+$o_virtual_machine:config, e_little]:u32 == $global_minimal_config_add &

// TODO fix this with fixed addresses
  mem[($global_vm_0_add + ($o_virtual_machine:mode_states) +
       (1:u32 * $t_hyper_mode_state_len)) + $o_hyper_mode_state:ctx + $o_context:pc,
       e_little]:u32 ==
    mem[$global_minimal_config_add+$o_hc_config:guest_entry_point, e_little]:u32 &
  mem[($global_vm_0_add + ($o_virtual_machine:mode_states) +
       (1:u32 * $t_hyper_mode_state_len)) + $o_hyper_mode_state:ctx + $o_context:sp,
       e_little]:u32 ==
    mem[$global_minimal_config_add+$o_hc_config:guest_entry_sp, e_little]:u32 &

// Real precondition of this iteration
    R2 == ($global_vm_1_add + ($o_virtual_machine:mode_states) + (1:u32 * $t_hyper_mode_state_len)) &
    mem[$global_vm_1_add + ($o_virtual_machine:mode_states)+($o_hyper_mode_state:mode_config), e_little]:u32 == $global_gm_interrupt_2_add &
    mem[$global_vm_1_add + ($o_virtual_machine:mode_states)+($o_hyper_mode_state:mode_config)  + (1:u32 * $t_hyper_mode_state_len), e_little]:u32 == $global_gm_task_2_add &
    mem[$global_vm_1_add+$o_virtual_machine:config, e_little]:u32 == $global_minimal_config_add + $t_hc_config_len &

    true)
  ) &
  true
)

jmp "pc_$start_pc"

#include "../out/arm_to_ir.il"

label lift_error
goal:bool = (~precondition) | false
jmp "end"


label success
postcondition:bool = (
  loc_code_memory &
  mem[$global_vm_0_add + $o_virtual_machine:next, e_little]:u32 == $global_vm_1_add &
  mem[$global_vm_0_add + $o_virtual_machine:current_mode_state, e_little]:u32 == 
       ($global_vm_0_add + ($o_virtual_machine:mode_states) +
       (1:u32 * $t_hyper_mode_state_len)) &
  mem[$global_vm_0_add + ($o_virtual_machine:mode_states)+($o_hyper_mode_state:mode_config), e_little]:u32 == $global_gm_interrupt_1_add &
  mem[$global_vm_0_add + ($o_virtual_machine:mode_states)+($o_hyper_mode_state:mode_config)  + (1:u32 * $t_hyper_mode_state_len), e_little]:u32 == $global_gm_task_1_add &
  mem[$global_vm_0_add + $o_virtual_machine:current_guest_mode, e_little]:u32 == 1:u32 &
  mem[$global_vm_0_add+$o_virtual_machine:config, e_little]:u32 == $global_minimal_config_add &

// TODO fix this with fixed addresses
  mem[($global_vm_0_add + ($o_virtual_machine:mode_states) +
       (1:u32 * $t_hyper_mode_state_len)) + $o_hyper_mode_state:ctx + $o_context:pc,
       e_little]:u32 ==
    mem[$global_minimal_config_add+$o_hc_config:guest_entry_point, e_little]:u32 &
  mem[($global_vm_0_add + ($o_virtual_machine:mode_states) +
       (1:u32 * $t_hyper_mode_state_len)) + $o_hyper_mode_state:ctx + $o_context:sp,
       e_little]:u32 ==
    mem[$global_minimal_config_add+$o_hc_config:guest_entry_sp, e_little]:u32 &


// TODO fixed part of vm1
  mem[$global_vm_1_add + $o_virtual_machine:next, e_little]:u32 == $global_vm_0_add &

  let old_curr_vm:u32 := old_R0 in (
  let curr_vm:u32 := R0 in (
    (~(old_curr_vm == $global_vm_0_add) | (curr_vm == $global_vm_1_add)) &
    (~(old_curr_vm == $global_vm_1_add) | (
        curr_vm == $global_vm_0_add &

//Effect after the second iteration
  mem[$global_vm_1_add + $o_virtual_machine:current_mode_state, e_little]:u32 == 
       ($global_vm_1_add + ($o_virtual_machine:mode_states) +
       (1:u32 * $t_hyper_mode_state_len)) &
  mem[$global_vm_1_add + ($o_virtual_machine:mode_states)+($o_hyper_mode_state:mode_config), e_little]:u32 == $global_gm_interrupt_2_add &
  mem[$global_vm_1_add + ($o_virtual_machine:mode_states)+($o_hyper_mode_state:mode_config)  + (1:u32 * $t_hyper_mode_state_len), e_little]:u32 == $global_gm_task_2_add &
  mem[$global_vm_1_add + $o_virtual_machine:current_guest_mode, e_little]:u32 == 1:u32 &
  mem[$global_vm_1_add+$o_virtual_machine:config, e_little]:u32 == $global_minimal_config_add + $t_hc_config_len &

// TODO fix this with fixed addresses
  mem[($global_vm_1_add + ($o_virtual_machine:mode_states) +
       (1:u32 * $t_hyper_mode_state_len)) + $o_hyper_mode_state:ctx + $o_context:pc,
       e_little]:u32 ==
    mem[$global_minimal_config_add+$t_hc_config_len+$o_hc_config:guest_entry_point, e_little]:u32 &
  mem[($global_vm_1_add + ($o_virtual_machine:mode_states) +
       (1:u32 * $t_hyper_mode_state_len)) + $o_hyper_mode_state:ctx + $o_context:sp,
       e_little]:u32 ==
    mem[$global_minimal_config_add+$t_hc_config_len+$o_hc_config:guest_entry_sp, e_little]:u32 &

   true
    ))
  ))
)

goal:bool = (~precondition) | postcondition

jmp "end"
label end

