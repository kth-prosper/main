#set start_pc=[[0xB70]]
#set last_pc=[[0xB94]]
#set print_add=[[0xE5C]]

#include "src/backup_state.il"
#include "out/loc_code_memory.il"
#include "out/loc_symbols.il"
#include "out/f_symbols.il"
#include "out/types.il"

#include "src/boot.pre.il"

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

#include "src/boot.post.il"
goal:bool = (~precondition) | postcondition
jmp "end"
label end
