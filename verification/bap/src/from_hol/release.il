#set last_pc=[[0xAC]]

//#assert_stop 0x6F8 [[true]]

#include "src/hol_backup_state2.il"
#include "../out/loc_code_memory.il"
#include "../out/f_symbols.il"

my_precondition:bool = (
#include "../out/from_hol2/release.pre.il"
)

precondition:bool = ((
  loc_code_memory &
  (SP_SVC:u32 <= (0x100000:u32 - 4:u32)) &
  (SP_SVC:u32 >= 0x0f0000:u32) &
  my_precondition)
)

jmp "pc_0x8"

#include "../out/arm_to_ir.il"
label lift_error
goal:bool = (~precondition) | false
jmp "end"

label success

#include "src/from_hol/pre_post.il"

postcondition:bool = (
  true
)

goal:bool = (~precondition) | postcondition
jmp "end"
label end
halt true