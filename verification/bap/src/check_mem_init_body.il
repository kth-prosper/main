
#set start_pc=[[0x994]]
#set last_pc=[[0xA28]]
#set print_add=[[0xE5C]]

#include "src/backup_state.il"
#include "../out/loc_symbols.il"
#include "../out/loc_code_memory.il"
#include "src/mem_init_loop_inv.il"
#include "src/manual_mem_lookup.inv.il"
#include "src/manual_mem_lookup.end.post.il"


// #assert_stop 0xA1C [[
//   R0 == 0x1:u32 &
//   R1 == 0x0:u32 &
//   Z_FLAG &
//   R6 == 0:u32 &
//   R4 == (low:u32(0x12:u64) | (1:u32 << low:u32(0xA:u64))) &
//   R2 == 0:u32 &
//   R3 == 1:u32 &
//   R5 == old_R5 +1:u32
// ]]

// Old approach that broute force all memory locations
// #set debug=[[
// res = []
// for j in range(0x512):
//     res.append("""
//   (
//     let add:u32 := %d:u32 in (
//        $ptcnd
//     )
//   )
// """%(j)) 
// il = il.replace("$foreach", "&\n".join(res))
// ]]
#set debug=[[
res = []
res.append("""
(
  true
)
""") 
il = il.replace("$foreach", "&\n".join(res))
il = il.replace("jmp  \"pc_0xBCC\"", """
f_pre:bool = ( $mem_conf )
tmp_f_param:u32 = R0
R0 = free_f_res:u32
f_post:bool = (
  let param:u32 := (tmp_f_param:u32 >> low:u32(0x14:u64)) in (
      $look_up_post
  )
)
""")
]]

// I can non use mem_conf2 for problem in variable substitution
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


  // CPU_TYPE and MODEL
  mem:?u32[(SP_SVC:u32 + low:u32(0x7:u64)) ,e_little]:u8 == 0:u8 &
  mem:?u32[(SP_SVC:u32 + low:u32(0x6:u64)) ,e_little]:u8 == 0:u8 &
  (old_SP_SVC:u32 <= (0x100000:u32 - 4:u32)) &
  (old_SP_SVC:u32 >= 0x0f0000:u32)
]]

precondition:bool = (
  ($foreach) &
  $other_mem &
  $mem_conf &
  loc_code_memory &
  (R7 == $global_flpt_add-4:u32 + 4:u32*R5) &

  (R5 < 0x200:u32) &
  (R5 >= 0x0:u32) &
  true
)

jmp "pc_$start_pc"

#include "src/mem_init_manual.il"

label lift_error
goal:bool = (~precondition) | false
jmp "end"


label success
postcondition:bool = 
(f_pre) & (
  (~f_post) |
  (
// Old approach that check all locations of the array
//   let add:u32 := free_add:u32 in (
// New approach that check only the last modified location
   let add:u32 := R5 - 1:u32 in (
      $ptcnd
   )
   &
     (R7 == $global_flpt_add-4:u32 + 4:u32*R5)
  )
)

goal:bool = (~precondition) | postcondition
jmp "end"
label end

