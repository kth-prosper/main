mem_rl1:?u32 = mem:?u32;
old_mem:?u32 = mem:?u32;
R0_RL1:u32 = R0:u32
R1_RL1:u32 = R1:u32
R2_RL1:u32 = R2:u32
R3_RL1:u32 = R3:u32
R4_RL1:u32 = R4:u32
R5_RL1:u32 = R5:u32
R6_RL1:u32 = R6:u32
R7_RL1:u32 = R7:u32
R8_RL1:u32 = R8:u32
R9_RL1:u32 = R9:u32
R10_RL1:u32 = R10:u32
R11_RL1:u32 = R11:u32
R12_RL1:u32 = R12:u32
LR_RL1:u32 = LR:u32
SP_RL1:u32 = SP:u32

PC_RL1:u32 = (LR_SVC:u32-4:u32)

N_RL1:bool  = SVC_N_FLAG:bool 
C_RL1:bool  = SVC_C_FLAG:bool 
Z_RL1:bool  = SVC_Z_FLAG:bool 
RV_RL1:bool  = SVC_V_FLAG:bool 
Q_RL1:bool  = SVC_Q_FLAG:bool 

old_CR0:u32 = CR0:u32
old_CR3:u32 = CR3:u32
loc_code_memory:bool = 
  (old_mem[0x208:u32, e_little]:u32 == 0x0000831c:u32) &
  (old_mem[0x20c:u32, e_little]:u32 == 0x00008320:u32) &
  (old_mem[0x210:u32, e_little]:u32 == 0xfffff000:u32) &
  (old_mem[0x214:u32, e_little]:u32 == 0x00002000:u32) &
  (old_mem[0x218:u32, e_little]:u32 == 0x00000084:u32) &
  (old_mem[0x21c:u32, e_little]:u32 == 0x00002004:u32) &
  (old_mem[0x220:u32, e_little]:u32 == 0x0000200c:u32) &
  (old_mem[0x224:u32, e_little]:u32 == 0x00002008:u32) &
  (old_mem[0x268:u32, e_little]:u32 == 0x0000831c:u32) &
  (old_mem[0x26c:u32, e_little]:u32 == 0x00008320:u32) &
  (old_mem[0x28c:u32, e_little]:u32 == 0x00002000:u32) &
  (old_mem[0x29c:u32, e_little]:u32 == 0x00002000:u32) &
  (old_mem[0x2ac:u32, e_little]:u32 == 0x00002000:u32) &
  (old_mem[0x3fc:u32, e_little]:u32 == 0x000010c0:u32) &
  (old_mem[0x45c:u32, e_little]:u32 == 0x000003d8:u32) &
  (old_mem[0x4e8:u32, e_little]:u32 == 0x000003d8:u32) &
  (old_mem[0x514:u32, e_little]:u32 == 0xfffe00ff:u32) &
  (old_mem[0x518:u32, e_little]:u32 == 0x00002010:u32) &
  (old_mem[0x590:u32, e_little]:u32 == 0xfffe00ff:u32) &
  (old_mem[0x594:u32, e_little]:u32 == 0x00004004:u32) &
  (old_mem[0x598:u32, e_little]:u32 == 0x00002010:u32) &
  (old_mem[0x59c:u32, e_little]:u32 == 0x000004ec:u32) &
  (old_mem[0x5b8:u32, e_little]:u32 == 0xfffe00ff:u32) &
  (old_mem[0x5e4:u32, e_little]:u32 == 0xfffe00ff:u32) &
  (old_mem[0x610:u32, e_little]:u32 == 0xfffd00ff:u32) &
  (old_mem[0x614:u32, e_little]:u32 == 0x00002014:u32) &
  (old_mem[0x634:u32, e_little]:u32 == 0xfffd00ff:u32) &
  (old_mem[0x68c:u32, e_little]:u32 == 0xfffd00ff:u32) &
  (old_mem[0x690:u32, e_little]:u32 == 0x00002014:u32) &
  (old_mem[0x6e0:u32, e_little]:u32 == 0x00008130:u32) &
  (old_mem[0x72c:u32, e_little]:u32 == 0x000010e4:u32) &
  (old_mem[0x754:u32, e_little]:u32 == 0x000010ff:u32) &
  (old_mem[0x77c:u32, e_little]:u32 == 0x00001122:u32) &
  (old_mem[0x834:u32, e_little]:u32 == 0x00008130:u32) &
  (old_mem[0x838:u32, e_little]:u32 == 0x00001145:u32) &
  (old_mem[0x860:u32, e_little]:u32 == 0x00001159:u32) &
  (old_mem[0x8a4:u32, e_little]:u32 == 0x00008130:u32) &
  (old_mem[0x8c4:u32, e_little]:u32 == 0x00008130:u32) &
  (old_mem[0x8e8:u32, e_little]:u32 == 0x00008130:u32) &
  (old_mem[0x8ec:u32, e_little]:u32 == 0x00001186:u32) &
  (old_mem[0x8fc:u32, e_little]:u32 == 0x000011b8:u32) &
  (old_mem[0x968:u32, e_little]:u32 == 0x00008130:u32) &
  (old_mem[0x96c:u32, e_little]:u32 == 0x00001221:u32) &
  (old_mem[0x970:u32, e_little]:u32 == 0x00001259:u32) &
  (old_mem[0x974:u32, e_little]:u32 == 0x00001279:u32) &
  (old_mem[0xa54:u32, e_little]:u32 == 0x00003ffc:u32) &
  (old_mem[0xa58:u32, e_little]:u32 == 0x0000136c:u32) &
  (old_mem[0xa5c:u32, e_little]:u32 == 0x55555555:u32) &
  (old_mem[0xa60:u32, e_little]:u32 == 0x00004000:u32) &
  (old_mem[0xa90:u32, e_little]:u32 == 0x00000758:u32) &
  (old_mem[0xa94:u32, e_little]:u32 == 0x00000730:u32) &
  (old_mem[0xa98:u32, e_little]:u32 == 0x000006e4:u32) &
  (old_mem[0xa9c:u32, e_little]:u32 == 0x0000083c:u32) &
  (old_mem[0xaa0:u32, e_little]:u32 == 0x00000780:u32) &
  (old_mem[0xb58:u32, e_little]:u32 == 0x00008134:u32) &
  (old_mem[0xb5c:u32, e_little]:u32 == 0x00008244:u32) &
  (old_mem[0xb60:u32, e_little]:u32 == 0x00008080:u32) &
  (old_mem[0xb64:u32, e_little]:u32 == 0x00008130:u32) &
  (old_mem[0xb9c:u32, e_little]:u32 == 0x00008130:u32) &
  (old_mem[0xbc8:u32, e_little]:u32 == 0x0000129d:u32) &
  (old_mem[0xc14:u32, e_little]:u32 == 0x000081e4:u32) &
  (old_mem[0xc44:u32, e_little]:u32 == 0x00001311:u32) &
  (old_mem[0xc48:u32, e_little]:u32 == 0x0000133f:u32) &
  (old_mem[0xcbc:u32, e_little]:u32 == 0x00002000:u32) &
  (old_mem[0xcc0:u32, e_little]:u32 == 0x00008000:u32) &
  (old_mem[0xcc4:u32, e_little]:u32 == 0x000ffffc:u32) &
  true 

















































































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


my_precondition:bool = (
 ((mem_rl1:?u32[low:u32(0x8080:u64),  e_little]:u32 == low:u32(0x8084:u64)) & 
(N_RL1:bool == N_ILA:bool) & 
(Z_RL1:bool == Z_ILA:bool) & 
(C_RL1:bool == C_ILA:bool) & 
(RV_RL1:bool == RV_ILA:bool) & 
(Q_RL1:bool == Q_ILA:bool) & 
(J_RL1:bool == J_ILA:bool) & 
(E_RL1:bool == E_ILA:bool) & 
(A_RL1:bool == A_ILA:bool) & 
(I_RL1:bool == I_ILA:bool) & 
(F_RL1:bool == F_ILA:bool) & 
(T_RL1:bool == T_ILA:bool) & 
(R0_RL1:u32 == R0_ILA:u32) & 
(R1_RL1:u32 == R1_ILA:u32) & 
(R2_RL1:u32 == R2_ILA:u32) & 
(R3_RL1:u32 == R3_ILA:u32) & 
(R4_RL1:u32 == R4_ILA:u32) & 
(R5_RL1:u32 == R5_ILA:u32) & 
(R6_RL1:u32 == R6_ILA:u32) & 
(R7_RL1:u32 == R7_ILA:u32) & 
(R8_RL1:u32 == R8_ILA:u32) & 
(R9_RL1:u32 == R9_ILA:u32) & 
(R10_RL1:u32 == R10_ILA:u32) & 
(R11_RL1:u32 == R11_ILA:u32) & 
(R12_RL1:u32 == R12_ILA:u32) & 
(SP_RL1:u32 == SP_ILA:u32) & 
(LR_RL1:u32 == LR_ILA:u32) & 
(PC_RL1:u32 == PC_ILA:u32) & 
(low:bool((mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x40:u64)),  e_little]:u32 & (0x1:u32 << (low:u32(0x1F:u64)))) >> low:u32(0x1F:u64)) == N_ILB:bool) & 
(low:bool((mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x40:u64)),  e_little]:u32 & (0x1:u32 << (low:u32(0x1E:u64)))) >> low:u32(0x1E:u64)) == Z_ILB:bool) & 
(low:bool((mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x40:u64)),  e_little]:u32 & (0x1:u32 << (low:u32(0x1D:u64)))) >> low:u32(0x1D:u64)) == C_ILB:bool) & 
(low:bool((mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x40:u64)),  e_little]:u32 & (0x1:u32 << (low:u32(0x1C:u64)))) >> low:u32(0x1C:u64)) == RV_ILB:bool) & 
(low:bool((mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x40:u64)),  e_little]:u32 & (0x1:u32 << (low:u32(0x1B:u64)))) >> low:u32(0x1B:u64)) == Q_ILB:bool) & 
(low:bool((mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x40:u64)),  e_little]:u32 & (0x1:u32 << (low:u32(0x18:u64)))) >> low:u32(0x18:u64)) == J_ILB:bool) & 
(low:bool((mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x40:u64)),  e_little]:u32 & (0x1:u32 << (low:u32(0x9:u64)))) >> low:u32(0x9:u64)) == E_ILB:bool) & 
(low:bool((mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x40:u64)),  e_little]:u32 & (0x1:u32 << (low:u32(0x8:u64)))) >> low:u32(0x8:u64)) == A_ILB:bool) & 
(low:bool((mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x40:u64)),  e_little]:u32 & (0x1:u32 << (low:u32(0x7:u64)))) >> low:u32(0x7:u64)) == I_ILB:bool) & 
(low:bool((mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x40:u64)),  e_little]:u32 & (0x1:u32 << (low:u32(0x6:u64)))) >> low:u32(0x6:u64)) == F_ILB:bool) & 
(low:bool((mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x40:u64)),  e_little]:u32 & (0x1:u32 << (low:u32(0x5:u64)))) >> low:u32(0x5:u64)) == T_ILB:bool) & 
(mem_rl1:?u32[mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32,  e_little]:u32 == R0_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x4:u64)),  e_little]:u32 == R1_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x8:u64)),  e_little]:u32 == R2_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0xC:u64)),  e_little]:u32 == R3_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x10:u64)),  e_little]:u32 == R4_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x14:u64)),  e_little]:u32 == R5_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x18:u64)),  e_little]:u32 == R6_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x1C:u64)),  e_little]:u32 == R7_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x20:u64)),  e_little]:u32 == R8_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x24:u64)),  e_little]:u32 == R9_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x28:u64)),  e_little]:u32 == R10_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x2C:u64)),  e_little]:u32 == R11_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x30:u64)),  e_little]:u32 == R12_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x34:u64)),  e_little]:u32 == SP_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x38:u64)),  e_little]:u32 == LR_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x181AC:u64),  e_little]:u32 + low:u32(0x3C:u64)),  e_little]:u32 == PC_ILB:u32) & 
(mem_rl1:?u32[low:u32(0x8080:u64),  e_little]:u32 == low:u32(0x8084:u64)) & 
(mem_rl1:?u32[low:u32(0x81BC:u64),  e_little]:u32 == MSG11:u32) & 
(mem_rl1:?u32[low:u32(0x181B8:u64),  e_little]:u32 == MSG21:u32) & 
((mem_rl1:?u32[low:u32(0x8130:u64),  e_little]:u32 == low:u32(0x8134:u64))|(mem_rl1:?u32[low:u32(0x8130:u64),  e_little]:u32 == low:u32(0x8080:u64))) & 
(mem_rl1:?u32[low:u32(0x81D8:u64),  e_little]:u32 == low:u32(0x8080:u64)) & 
((mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64))|(mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8188:u64))) & 
(mem_rl1:?u32[low:u32(0x81D4:u64),  e_little]:u32 == low:u32(0x8244:u64)) & 
(mem_rl1:?u32[low:u32(0x8124:u64),  e_little]:u32 == low:u32(0x8134:u64)) & 
((mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64))|(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x80D4:u64))) & 
(mem_rl1:?u32[low:u32(0x8120:u64),  e_little]:u32 == low:u32(0x82B0:u64)) & 
(mem_rl1:?u32[low:u32(0x831C:u64),  e_little]:u32 == low:u32(0x0:u64)) & 
(~((mem_rl1:?u32[low:u32(0x8130:u64),  e_little]:u32 == low:u32(0x8134:u64))) | (mem_rl1:?u32[low:u32(0x8324:u64),  e_little]:u32 == mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32)) & 
(~((mem_rl1:?u32[low:u32(0x8130:u64),  e_little]:u32 == low:u32(0x8080:u64))) | (mem_rl1:?u32[low:u32(0x8324:u64),  e_little]:u32 == mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32)) & 
(mem_rl1:?u32[low:u32(0xFFFFF100:u64),  e_little]:u32 == low:u32(0x780:u64)) & 
(mem_rl1:?u32[low:u32(0x2008:u64),  e_little]:u32 == low:u32(0x6E4:u64)) & 
(mem_rl1:?u32[low:u32(0x8298:u64),  e_little]:u32 == low:u32(0x0:u64)) & 
(mem_rl1:?u32[low:u32(0x8304:u64),  e_little]:u32 == low:u32(0x0:u64)) & 
(mem_rl1:?u32[low:u32(0x13A0:u64),  e_little]:u32 == low:u32(0x5:u64)) & 
(mem_rl1:?u32[low:u32(0x13B4:u64),  e_little]:u32 == low:u32(0x5:u64)) & 
(mem_rl1:?u32[low:u32(0x13C8:u64),  e_little]:u32 == low:u32(0x11:u64)) & 
(mem_rl1:?u32[low:u32(0x13DC:u64),  e_little]:u32 == low:u32(0x11:u64))
 ) &
  ((old_mem[LR_SVC:u32-4:u32, e_little]:u32 & 0xFFFFFF:u32) == 0x1:u32)
)

precondition:bool = ((
  loc_code_memory &
  hyper_invariants &
  my_precondition)
)



PC:u32=LR_SVC:u32

