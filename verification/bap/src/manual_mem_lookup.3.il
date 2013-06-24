#set start_pc=[[0xC0C]]
#set last_pc=[[0xC10]]
#set print_add=[[0xE5C]]

#include "src/backup_state.il"
#include "out/loc_code_memory.il"
#include "out/loc_symbols.il"
#include "out/f_symbols.il"
#include "out/types.il"

#include "src/manual_mem_lookup.inv.il"
#include "src/manual_mem_lookup.end.post.il"

my_precondition:bool = (
  $loop_inv
  &
  (~to_loop) &
  old_mem[$global___data_start___add+0:u32+(0:u32 * 4:u32*4:u32), e_little]:u32 == 0:u32 &
  old_mem[$global___data_start___add+4:u32+(0:u32 * 4:u32*4:u32), e_little]:u32 == 0xff:u32 &
  old_mem[$global___data_start___add+0:u32+(1:u32 * 4:u32*4:u32), e_little]:u32 == 0x100:u32 &
  old_mem[$global___data_start___add+4:u32+(1:u32 * 4:u32*4:u32), e_little]:u32 == 0xff:u32 &
  old_mem[$global___data_start___add+0:u32+(2:u32 * 4:u32*4:u32), e_little]:u32 == 0x200:u32 &
  old_mem[$global___data_start___add+4:u32+(2:u32 * 4:u32*4:u32), e_little]:u32 == 0xff:u32
)


precondition:bool = (
  loc_code_memory &
  my_precondition
)

jmp "pc_$start_pc"

#include "src/manual_mem_loockup.il"
label lift_error
goal:bool = (~precondition) | false
jmp "end"

label success

postcondition:bool = (
  old_mem[fv:u32, e_little]:u8 == mem[fv:u32, e_little]:u8 &
  $look_up_post
  &
  true
)

goal:bool = (~precondition) | postcondition
jmp "end"
label end
