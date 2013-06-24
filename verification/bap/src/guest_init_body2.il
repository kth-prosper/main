#set start_pc=[[0xAE0]]
#set last_pc=[[0xB44]]
#set print_add=[[0xE5C]]

#include "src/backup_state.il"
#include "../out/loc_symbols.il"
#include "../out/loc_code_memory.il"
#include "../out/types.il"


precondition:bool = (
  loc_code_memory &
  mem[$global_minimal_config_add + $o_hc_config:guest_modes, e_little]:u32 == $global_gm_interrupt_1_add &
  mem[$global_minimal_config_add + $o_hc_config:guest_modes + 4:u32, e_little]:u32 == $global_gm_task_1_add &

  mem[$global_vm_0_add + $o_virtual_machine:next, e_little]:u32 == $global_vm_1_add &
  mem[$global_vm_0_add + $o_virtual_machine:config, e_little]:u32 == $global_minimal_config_add &

  mem[$global_vm_1_add + $o_virtual_machine:next, e_little]:u32 == $global_vm_0_add &

  R3 == 0:u32 &
  R0 == $global_vm_0_add &
  true
)

jmp "pc_$start_pc"

#include "../out/arm_to_ir.il"

label lift_error
t_goal:bool = (~precondition) | false
jmp "end"


label success
postcondition:bool = (
  loc_code_memory &
  mem[$global_vm_0_add + $o_virtual_machine:next, e_little]:u32 == $global_vm_1_add &
  mem[$global_vm_0_add+$o_virtual_machine:config, e_little]:u32 == $global_minimal_config_add &

  mem[$global_vm_0_add + $o_virtual_machine:current_mode_state, e_little]:u32 == 
       ($global_vm_0_add + ($o_virtual_machine:mode_states) +
       (1:u32 * $t_hyper_mode_state_len)) &

  mem[$global_vm_0_add + ($o_virtual_machine:mode_states)+($o_hyper_mode_state:mode_config), e_little]:u32 == $global_gm_interrupt_1_add &
  mem[$global_vm_0_add + ($o_virtual_machine:mode_states)+($o_hyper_mode_state:mode_config)  + (1:u32 * $t_hyper_mode_state_len), e_little]:u32 == $global_gm_task_1_add &
  mem[$global_vm_0_add + $o_virtual_machine:current_guest_mode, e_little]:u32 == 1:u32 &

// TODO fix this with fixed addresses
  mem[($global_vm_0_add + ($o_virtual_machine:mode_states) +
       (1:u32 * $t_hyper_mode_state_len)) + $o_hyper_mode_state:ctx + $o_context:pc,
       e_little]:u32 ==
    mem[$global_minimal_config_add+$o_hc_config:guest_entry_point, e_little]:u32 &
  mem[($global_vm_0_add + ($o_virtual_machine:mode_states) +
       (1:u32 * $t_hyper_mode_state_len)) + $o_hyper_mode_state:ctx + $o_context:sp,
       e_little]:u32 ==
    mem[$global_minimal_config_add+$o_hc_config:guest_entry_sp, e_little]:u32 &

  true
)

t_goal:bool = (~precondition) | true

jmp "end"
label end

goal:bool = t_goal:bool