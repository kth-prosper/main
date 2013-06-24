
inv_others:bool = (
  (LR_SVC:u32 >= 0x10000000:u32) &
  (LR_SVC:u32 < 0x30000000:u32) &
  (SP_SVC:u32 <= (0x100000:u32 - 4:u32)) &
  (SP_SVC:u32 >= 0x0f0000:u32) &

  (mem[0x18234:u32, e_little]:u32 == 0x00100000:u32) & 
  (mem[0x18238:u32, e_little]:u32 == 0x002ffffc:u32) &
  (mem[0x1823c:u32, e_little]:u32 == 0x00000001:u32) &	 
  (mem[0x18280:u32, e_little]:u32 == 0x00001374:u32) &
  (mem[0x18284:u32, e_little]:u32 == 0x00001388:u32) &
  (mem[0x18288:u32, e_little]:u32 == 0x00000000:u32) &
  (mem[0x1828c:u32, e_little]:u32 == 0x003ffffc:u32) &
  (mem[0x18290:u32, e_little]:u32 == 0x00200000:u32) &
  (mem[0x182a0:u32, e_little]:u32 == 0x00400000:u32) &
  (mem[0x182a4:u32, e_little]:u32 == 0x005ffffc:u32) &
  (mem[0x182a8:u32, e_little]:u32 == 0x00000001:u32) &
  (mem[0x182ec:u32, e_little]:u32 == 0x0000139c:u32) &
  (mem[0x182f0:u32, e_little]:u32 == 0x000013b0:u32) &
  (mem[0x182f4:u32, e_little]:u32 == 0x00000000:u32) &
  (mem[0x182f8:u32, e_little]:u32 == 0x006ffffc:u32) &
  (mem[0x182fc:u32, e_little]:u32 == 0x00500000:u32) &

  true
)

hyper_invariants:bool = (
  inv_others
)
