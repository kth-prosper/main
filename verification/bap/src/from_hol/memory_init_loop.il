
// #assert_stop 0xA44 [[R3:u32 <> free_var:u32]]
#assert_stop 0x8E0 [[(mem:?u32[(SP_SVC:u32 + low:u32(0x7:u64)),  e_little]:u8 == low:u8(0x0:u64))]]

// ((low:u32(0x3:u64) & R4:u32) == low:u32(0x2:u64)) |
// #assert_stop 0x8E0 [[
// (R4 <> free_var:u32)
// ]]

// WARNING error in the lifter an intruxtion tmpr1= became r1= when accessing to single bytes

// #assert_stop 0x8E4 [[
// (low:u32(0x3:u64) & R4:u32) == 2:u32
// ]]

#include "src/hol_backup_state2.il"
#include "../out/loc_code_memory.il"
#include "../out/f_symbols.il"
#include "../out/loc_symbols.il"

my_precondition:bool = (
#include "../out/from_hol2/memory_init_loop.pre.il"
)

precondition:bool = ((
  loc_code_memory &
  (SP_SVC:u32 <= (0x100000:u32 - 4:u32)) &
  (SP_SVC:u32 >= 0x0f0000:u32) &
  my_precondition)
& 
#include "../out/const_CSWTCH12.il"
&
#include "../out/const_CSWTCH13.il"
&
#include "../out/const___data_start__.il"
&
#include "../out/const_minimal_config.il"
)


// To be fixed, this shoud be part of hol
#set debug=[[
loc = bap_add_to_int(vars["f_mem_padr_lookup_add"])
label = add_to_bap_label(loc)
hcfg = vars["global___data_start___add"]
il = il.replace('jmp  "%s"' % label, """
R0:u32 = if (R0 >= 0x100000:u32 & R0 < 0x400000:u32) then
       %s + 16:u32
       else if (R0 >= 0x400000:u32 & R0 < 0x700000:u32) then
       %s + 32:u32
       else
       %s
\n
""" % (hcfg, hcfg, hcfg)
)


loc = bap_add_to_int(vars["f_memory_init_add"])
vars["start_pc"] = add_to_bap_no_type(loc+180)
vars["last_pc"] = add_to_bap_no_type(loc+216)

vars["start_pc"] = add_to_bap_no_type(0x850)
vars["last_pc"] = add_to_bap_no_type(0x8E4)
]]

jmp "pc_$start_pc"

#include "../out/arm_to_ir.il"
label lift_error
goal:bool = (~precondition) | false
jmp "end"

label success

#include "src/from_hol/pre_post.il"

//#include "../out/from_hol2/memory_init_loop.post.0.il" OK
//#include "../out/from_hol2/memory_init_loop.post.1.il" OK
//#include "../out/from_hol2/memory_init_loop.post.2.il" OK
//#include "../out/from_hol2/memory_init_loop.post.3.il" OK
//#include "../out/from_hol2/memory_init_loop.post.4.il" failed

postcondition:bool = (
#include "../out/from_hol2/memory_init_loop.post.4.il"
)

goal:bool = (~precondition) | postcondition
jmp "end"
label end
halt true