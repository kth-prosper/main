#set start_pc=[[0x994]]
#set last_pc=[[0x998]]

#include "out/loc_symbols.il"
#include "src/manual_mem_lookup.end.post.il"
#include "src/mem_init_loop_inv.il"

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

precondition:bool = (
  $foreach
)

jmp "pc_$start_pc"

#include "src/mem_init_manual.il"

label success


fprecondition:bool = (
  true
)

postcondition:bool = (
//   let param:u32 := (R0:u32 >> low:u32(0x14:u64)) in
//   (
//     fprecondition &
//     // forall variables updated by the function
//     let R0:u32 := free_fupd_R0:u32 in
//     (
// 	(~($look_up_post)) | (
// #include "out/mem_init.loop.2.post.il"
// 	)
//     )
//   )
     let pre_mem:?u32:= mem in (
#include "out/mem_init.loop.2.post.il"
     )
)

goal:bool = (~precondition | postcondition)

