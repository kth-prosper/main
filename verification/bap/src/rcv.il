#set start_pc=[[0x18]]
#set last_pc=[[0xAC]]
#set print_add=[[0xE5C]]

//#assert_stop 0x64 [[R1 <> free_ind_jmp:u32]]
//#assert_stop 0x7A4 [[~Z_FLAG:bool]]
#assert_stop 0x814 [[false]]
//#assert_stop 0x7B0 [[Z_FLAG:bool]]
//#assert_stop 0xD3C [[LR_SVC <> free_ind_jmp:u32]]
//#assert_stop 0x24C [[LR_SVC <> free_ind_jmp:u32]]
//#assert_stop 0xCCC [[LR_SVC <> free_ind_jmp:u32]]
//#assert_stop 0x810 [[PC <> free_ind_jmp:u32]]



#ind_jmp 0x64 [[R1]] $f_irq_handler_add
#ind_jmp 0xD3C [[LR_SVC]] 0x7CC:u32
#ind_jmp 0x24C [[LR_SVC]] 0x888:u32
#ind_jmp 0xCCC [[LR_SVC]] 0x7E8:u32
#ind_jmp 0x810 [[PC]] 0x68:u32

#include "src/backup_state.il"
#include "out/loc_code_memory.il"
#include "out/loc_symbols.il"
#include "out/f_symbols.il"
#include "out/types.il"
#include "src/hyper_invariants.il"

#include "src/rcv.pre.il"

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

#include "src/rcv.post.il"
goal:bool = (~precondition) | postcondition
jmp "end"
label end
