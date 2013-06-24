#set start_pc=[[0x978]]
#set last_pc=[[0x990]]
#set print_add=[[0xE5C]]

#include "src/backup_state.il"
#include "../out/loc_symbols.il"
#include "../out/loc_code_memory.il"
#include "src/mem_init_loop_inv.il"
#include "src/manual_mem_lookup.inv.il"
#include "src/manual_mem_lookup.end.post.il"

//#assert_stop 0x27C [[LR_SVC <> ind_jmp_free:u32]]


#ind_jmp 0x27C [[LR_SVC]] 0x00000988:u32


#set other_mem = [[
  mem[$global___data_start___add+0x8:u32+(0:u32 * 4:u32*4:u32), e_little]:u32 == 1:u32 &
  mem[$global___data_start___add+0x8:u32+(1:u32 * 4:u32*4:u32), e_little]:u32 == 3:u32 &
  mem[$global___data_start___add+0x8:u32+(2:u32 * 4:u32*4:u32), e_little]:u32 == 4:u32

  &
  mem[$global_CSWTCH12_add+0:u32*4:u32, e_little]:u32 == 0x00000000:u32 &
  mem[$global_CSWTCH12_add+1:u32*4:u32, e_little]:u32 == 0x00000002:u32 &
  mem[$global_CSWTCH12_add+2:u32*4:u32, e_little]:u32 == 0x00000001:u32 &
  mem[$global_CSWTCH12_add+3:u32*4:u32, e_little]:u32 == 0x00000002:u32 &
  mem[$global_CSWTCH12_add+4:u32*4:u32, e_little]:u32 == 0x00000002:u32 &
  mem[$global_CSWTCH12_add+5:u32*4:u32, e_little]:u32 == 0x00000000:u32 &

  mem[$global_CSWTCH13_add+0:u32*4:u32, e_little]:u32 == 0x1:u32 &
  mem[$global_CSWTCH13_add+1:u32*4:u32, e_little]:u32 == 0x00000000:u32 &
  mem[$global_CSWTCH13_add+2:u32*4:u32, e_little]:u32 == 0x00000003:u32 &
  mem[$global_CSWTCH13_add+3:u32*4:u32, e_little]:u32 == 0x00000003:u32 &
  mem[$global_CSWTCH13_add+4:u32*4:u32, e_little]:u32 == 0x00000000:u32 &
  mem[$global_CSWTCH13_add+5:u32*4:u32, e_little]:u32 == 0x00000003:u32 &

  (old_SP_SVC:u32 <= (0x100000:u32 - 4:u32)) &
  (old_SP_SVC:u32 >= 0x0f0000:u32)
]]

precondition:bool = (
  $mem_conf &
  $other_mem &
  loc_code_memory &
  true
)

jmp "pc_$start_pc"

#include "../out/arm_to_ir.il"

label lift_error
goal:bool = (~precondition) | false
jmp "end"


label success
postcondition:bool = (
  mem:?u32[(SP_SVC:u32 + low:u32(0x7:u64)) ,e_little]:u8 == 0:u8 &
  mem:?u32[(SP_SVC:u32 + low:u32(0x6:u64)) ,e_little]:u8 == 0:u8 &
  $mem_conf &
  $other_mem &
  loc_code_memory &
  (R7 == $global_flpt_add-4:u32 + 4:u32*R5) &
  (R5 < 0x200:u32) &
  (R5 >= 0x0:u32)
)
//postcondition:bool = true

goal:bool = (~precondition) | postcondition

jmp "end"
label end

