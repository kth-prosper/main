#set start_pc=[[0xA2C]]
#set last_pc=[[0xA50]]
#set print_add=[[0xE5C]]

#include "src/backup_state.il"
#include "../out/loc_symbols.il"
#include "../out/loc_code_memory.il"
#include "src/mem_init_loop_inv.il"
#include "src/manual_mem_lookup.inv.il"
#include "src/manual_mem_lookup.end.post.il"


//#assert_stop 0xCEC [[LR_SVC <> ind_free_var:u32]]

#ind_jmp 0xCCC [[LR_SVC]] 0x00000A34:u32
#ind_jmp 0xCD4 [[LR_SVC]] 0x00000A3C:u32
#ind_jmp 0xCEC [[LR_SVC]] 0x00000A50:u32


#set debug=[[
il = il.replace("jmp  \"pc_0x2DC\"", "")
]]

precondition:bool = (
  loc_code_memory
)

jmp "pc_$start_pc"

#include "../out/arm_to_ir.il"

label lift_error
goal:bool = (~precondition) | false
jmp "end"


label success
postcondition:bool = (
  loc_code_memory &
  CR3 == 0x55555555:u32 &
  CR2 == $global_flpt_add
)

goal:bool = (~precondition) | postcondition

jmp "end"
label end

