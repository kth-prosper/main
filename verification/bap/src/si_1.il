#set start_pc=[[0x8]]
#set last_pc=[[0xAC]]
#set print_add=[[0xE5C]]

#ind_jmp 0x204 [[R12]] $f_swi_handler_add
#ind_jmp 0x8C0 [[LR_SVC]] $f_exception_bottom_add

//#assert_stop 0x1EC [[PC:u32 + low:u32(0x38:u64) == 0x224:u32]]
//#assert_stop 0x1EC [[R12 == 0x00002008:u32]]
//#assert_stop 0x1F0 [[R12 == 0x6E4:u32]]
//#assert_stop 0x204 [[R12 == 0x6E4:u32]]
//#assert_stop 0x6F8 [[true]]
//#assert_stop 0x70C [[true]]
//#assert_stop 0x8C0 [[LR_SVC <> free_ind_jmp:u32]]
//#assert_stop 0x84 [[true]]

#include "src/backup_state.il"
#include "out/loc_code_memory.il"
#include "out/loc_symbols.il"
#include "out/f_symbols.il"
#include "out/types.il"
#include "src/hyper_invariants.il"

#include "src/si_1.pre.il"

precondition:bool = (
  loc_code_memory &
  hyper_invariants &
  my_precondition
)

jmp "pc_$start_pc"

#include "out/arm_to_ir.il"
label lift_error
goal:bool = (~precondition) | false
jmp "end"

label success

#include "src/si_1.post.il"
goal:bool = (~precondition) | postcondition
jmp "end"
label end
