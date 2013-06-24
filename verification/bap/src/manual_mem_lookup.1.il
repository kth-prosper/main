#set start_pc=[[0xBCC]]
#set last_pc=[[0xBD4]]
#set print_add=[[0xE5C]]

//#assert_stop 0xC08 [[true]]

#include "src/backup_state.il"
#include "out/loc_code_memory.il"
#include "out/loc_symbols.il"
#include "out/f_symbols.il"
#include "out/types.il"

#include "src/manual_mem_lookup.inv.il"

my_precondition:bool = (
  $mem_conf &
  f_param:u32 == R0:u32
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

to_loop:bool = true

postcondition:bool = (
  let param:u32 := (f_param:u32 >> low:u32(0xC:u64)) in (
      $loop_inv
  )
)

goal:bool = (~precondition) | postcondition
jmp "end"
label end
