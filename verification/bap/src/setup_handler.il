#set start_pc=[[0xA64]]
#set last_pc=[[0x58C]]
#set print_add=[[0xE5C]]

//#assert_stop 0x288 [[LR_SVC <> free_ind_jump:u32]]
//#assert_stop 0x298 [[LR_SVC <> free_ind_jump:u32]]
//#assert_stop 0x2A8 [[LR_SVC <> free_ind_jump:u32]]
//#assert_stop 0x458 [[LR_SVC <> free_ind_jump:u32]]
//#assert_stop 0x4A0 [[LR_SVC <> free_ind_jump:u32]]


#ind_jmp 0x288 [[LR_SVC]] 0xA74:u32
#ind_jmp 0x298 [[LR_SVC]] 0xA7C:u32
#ind_jmp 0x2A8 [[LR_SVC]] 0xA84:u32
#ind_jmp 0x458 [[LR_SVC]] 0x554:u32
#ind_jmp 0x4A0 [[LR_SVC]] 0x568:u32
#ind_jmp 0x438 [[LR_SVC]] 0x57C:u32


#include "src/backup_state.il"
#include "out/loc_code_memory.il"
#include "out/loc_symbols.il"
#include "out/f_symbols.il"
#include "out/types.il"

#include "src/setup_handler.pre.il"

precondition:bool = (
  loc_code_memory &
  my_precondition
)

jmp "pc_$start_pc"

#include "out/arm_to_ir.il"
label lift_error
goal:bool = (~precondition) | false
jmp "end"

label success

#include "src/setup_handler.post.il"
goal:bool = (~precondition) | postcondition
jmp "end"
label end
