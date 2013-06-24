#set start_pc=[[0x9A0]]
#set last_pc=[[0xA28]]
#set print_add=[[0xE5C]]

mem:?u32 = pre_mem:?u32

#include "src/backup_state.il"
#include "out/loc_symbols.il"
#include "out/loc_code_memory.il"
#include "src/mem_init_loop_inv.il"
#include "src/manual_mem_lookup.end.post.il"


// #assert_stop 0x9D8 [[
//     true
//     & (Z_FLAG)
//     & (C_FLAG)
//     & (R0 == 3:u32)
//     & (R3 == 0x3:u32)
//     & (R1 == 0x0:u32)
//     & (R2 == 0x1:u32)
// ]]

#set debug=[[
res = []
for j in range(0x200):
    res.append("""
  (
    let add:u32 := %d:u32 in (
       $ptcnd
    )
  )
"""%(j)) 
il = il.replace("$foreach", "&\n".join(res))
]]

#set mem_conf = [[
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
  ((~(R5 >= 0:u32 & R5 <= 0xff:u32)) | (R0 == $global___data_start___add)) &
  ((~(R5 >= 0x100:u32 & R5 <= 0x1ff:u32)) | (R0 == $global___data_start___add + (1:u32 * 4:u32*4:u32))) &
  $mem_conf &
  loc_code_memory &
  (R6 == R5 << 20:u32) &
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
postcondition:bool = (
   let add:u32 := free_add:u32 in (
      $ptcnd
   ) &
   (R7 == $global_flpt_add-4:u32 + 4:u32*R5)
)

goal:bool = (~precondition) | postcondition
jmp "end"
label end
