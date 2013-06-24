#include "out/loc_symbols.il"
#include "src/mem_init_loop_inv.il"

#set debug=[[
res = []
for j in range(4096):
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


