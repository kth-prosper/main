












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


my_precondition:bool = ((mem_rl1:?u32[low:u32(0x8130:u64),  e_little]:u32 == low:u32(0x8134:u64)) & 
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
(low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32),  e_little]:u32 & (0x1:u32 << (low:u32(0x1F:u64)))) >> low:u32(0x1F:u64)) == N_ILB:bool) & 
(low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32),  e_little]:u32 & (0x1:u32 << (low:u32(0x1E:u64)))) >> low:u32(0x1E:u64)) == Z_ILB:bool) & 
(low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32),  e_little]:u32 & (0x1:u32 << (low:u32(0x1D:u64)))) >> low:u32(0x1D:u64)) == C_ILB:bool) & 
(low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32),  e_little]:u32 & (0x1:u32 << (low:u32(0x1C:u64)))) >> low:u32(0x1C:u64)) == RV_ILB:bool) & 
(low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32),  e_little]:u32 & (0x1:u32 << (low:u32(0x1B:u64)))) >> low:u32(0x1B:u64)) == Q_ILB:bool) & 
(low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32),  e_little]:u32 & (0x1:u32 << (low:u32(0x18:u64)))) >> low:u32(0x18:u64)) == J_ILB:bool) & 
(low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32),  e_little]:u32 & (0x1:u32 << (low:u32(0x9:u64)))) >> low:u32(0x9:u64)) == E_ILB:bool) & 
(low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32),  e_little]:u32 & (0x1:u32 << (low:u32(0x8:u64)))) >> low:u32(0x8:u64)) == A_ILB:bool) & 
(low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32),  e_little]:u32 & (0x1:u32 << (low:u32(0x7:u64)))) >> low:u32(0x7:u64)) == I_ILB:bool) & 
(low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32),  e_little]:u32 & (0x1:u32 << (low:u32(0x6:u64)))) >> low:u32(0x6:u64)) == F_ILB:bool) & 
(low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32),  e_little]:u32 & (0x1:u32 << (low:u32(0x5:u64)))) >> low:u32(0x5:u64)) == T_ILB:bool) & 
(mem_rl1:?u32[mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32,  e_little]:u32 == R0_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 + low:u32(0x4:u64)),  e_little]:u32 == R1_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 + low:u32(0x8:u64)),  e_little]:u32 == R2_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 + low:u32(0xC:u64)),  e_little]:u32 == R3_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 + low:u32(0x10:u64)),  e_little]:u32 == R4_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 + low:u32(0x14:u64)),  e_little]:u32 == R5_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 + low:u32(0x18:u64)),  e_little]:u32 == R6_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 + low:u32(0x1C:u64)),  e_little]:u32 == R7_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 + low:u32(0x20:u64)),  e_little]:u32 == R8_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 + low:u32(0x24:u64)),  e_little]:u32 == R9_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 + low:u32(0x28:u64)),  e_little]:u32 == R10_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 + low:u32(0x2C:u64)),  e_little]:u32 == R11_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 + low:u32(0x30:u64)),  e_little]:u32 == R12_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 + low:u32(0x34:u64)),  e_little]:u32 == SP_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 + low:u32(0x38:u64)),  e_little]:u32 == LR_ILB:u32) & 
(mem_rl1:?u32[(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 + low:u32(0x3C:u64)),  e_little]:u32 == PC_ILB:u32) & 
(mem_rl1:?u32[low:u32(0x8130:u64),  e_little]:u32 == low:u32(0x8134:u64)) & 
(mem_rl1:?u32[low:u32(0x81DC:u64),  e_little]:u32 == MSG11:u32) & 
(mem_rl1:?u32[low:u32(0x8128:u64),  e_little]:u32 == MSG21:u32) & 
(~(mem_rl1:?u32[low:u32(0x81E0:u64),  e_little]:u32 == low:u32(0x0:u64)) == FLG11:bool) & 
(~(mem_rl1:?u32[low:u32(0x812C:u64),  e_little]:u32 == low:u32(0x0:u64)) == FLG21:bool) & 
((mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8188:u64)) == RDY11:bool) & 
((mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x80D4:u64)) == RDY21:bool) & 
(mem_rl1:?u32[( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64)),  e_little]:u32 == CR0C11:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64)) + low:u32(0x4:u64)),  e_little]:u32 == CR1C11:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64)) + low:u32(0x8:u64)),  e_little]:u32 == CR2C11:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64)) + low:u32(0xC:u64)),  e_little]:u32 == CR3C11:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64)) + low:u32(0x10:u64)),  e_little]:u32 == CR4C11:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64)) + low:u32(0x14:u64)),  e_little]:u32 == CR5C11:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64)) + low:u32(0x18:u64)),  e_little]:u32 == CR6C11:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64)) + low:u32(0x1C:u64)),  e_little]:u32 == CR7C11:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64)) + low:u32(0x20:u64)),  e_little]:u32 == CR8C11:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64)) + low:u32(0x24:u64)),  e_little]:u32 == CR9C11:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64)) + low:u32(0x28:u64)),  e_little]:u32 == CR10C11:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64)) + low:u32(0x2C:u64)),  e_little]:u32 == CR11C11:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64)) + low:u32(0x30:u64)),  e_little]:u32 == CR12C11:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64)) + low:u32(0x34:u64)),  e_little]:u32 == CSPC11:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64)) + low:u32(0x38:u64)),  e_little]:u32 == CLRC11:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64)) + low:u32(0x3C:u64)),  e_little]:u32 == CPCC11:u32) & 
(mem_rl1:?u32[( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64)),  e_little]:u32 == CR0C21:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64)) + low:u32(0x4:u64)),  e_little]:u32 == CR1C21:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64)) + low:u32(0x8:u64)),  e_little]:u32 == CR2C21:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64)) + low:u32(0xC:u64)),  e_little]:u32 == CR3C21:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64)) + low:u32(0x10:u64)),  e_little]:u32 == CR4C21:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64)) + low:u32(0x14:u64)),  e_little]:u32 == CR5C21:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64)) + low:u32(0x18:u64)),  e_little]:u32 == CR6C21:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64)) + low:u32(0x1C:u64)),  e_little]:u32 == CR7C21:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64)) + low:u32(0x20:u64)),  e_little]:u32 == CR8C21:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64)) + low:u32(0x24:u64)),  e_little]:u32 == CR9C21:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64)) + low:u32(0x28:u64)),  e_little]:u32 == CR10C21:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64)) + low:u32(0x2C:u64)),  e_little]:u32 == CR11C21:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64)) + low:u32(0x30:u64)),  e_little]:u32 == CR12C21:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64)) + low:u32(0x34:u64)),  e_little]:u32 == CSPC21:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64)) + low:u32(0x38:u64)),  e_little]:u32 == CLRC21:u32) & 
(mem_rl1:?u32[(( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64)) + low:u32(0x3C:u64)),  e_little]:u32 == CPCC21:u32) & 
(NC11:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x1F:u64)))) >> low:u32(0x1F:u64))) & 
(ZC11:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x1E:u64)))) >> low:u32(0x1E:u64))) & 
(CC11:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x1D:u64)))) >> low:u32(0x1D:u64))) & 
(RVC11:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x1C:u64)))) >> low:u32(0x1C:u64))) & 
(QC11:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x1B:u64)))) >> low:u32(0x1B:u64))) & 
(JC11:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x18:u64)))) >> low:u32(0x18:u64))) & 
(EC11:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x9:u64)))) >> low:u32(0x9:u64))) & 
(AC11:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x8:u64)))) >> low:u32(0x8:u64))) & 
(IC11:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x7:u64)))) >> low:u32(0x7:u64))) & 
(FC11:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x6:u64)))) >> low:u32(0x6:u64))) & 
(TC11:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64)) then low:u32(0x8188:u64) else low:u32(0x8140:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x5:u64)))) >> low:u32(0x5:u64))) & 
(NC21:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x1F:u64)))) >> low:u32(0x1F:u64))) & 
(ZC21:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x1E:u64)))) >> low:u32(0x1E:u64))) & 
(CC21:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x1D:u64)))) >> low:u32(0x1D:u64))) & 
(RVC21:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x1C:u64)))) >> low:u32(0x1C:u64))) & 
(QC21:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x1B:u64)))) >> low:u32(0x1B:u64))) & 
(JC21:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x18:u64)))) >> low:u32(0x18:u64))) & 
(EC21:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x9:u64)))) >> low:u32(0x9:u64))) & 
(AC21:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x8:u64)))) >> low:u32(0x8:u64))) & 
(IC21:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x7:u64)))) >> low:u32(0x7:u64))) & 
(FC21:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x6:u64)))) >> low:u32(0x6:u64))) & 
(TC21:bool == low:bool((mem_rl1:?u32[(low:u32(0x40:u64) + ( if (mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64)) then low:u32(0x80D4:u64) else low:u32(0x808C:u64))),  e_little]:u32 & (0x1:u32 << (low:u32(0x5:u64)))) >> low:u32(0x5:u64))) & 
RDY21:bool & 
FLG21:bool & 
((mem_rl1:?u32[low:u32(0x8130:u64),  e_little]:u32 == low:u32(0x8134:u64))|(mem_rl1:?u32[low:u32(0x8130:u64),  e_little]:u32 == low:u32(0x8080:u64))) & 
(mem_rl1:?u32[low:u32(0x81D8:u64),  e_little]:u32 == low:u32(0x8080:u64)) & 
((mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8140:u64))|(mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == low:u32(0x8188:u64))) & 
(mem_rl1:?u32[low:u32(0x81D4:u64),  e_little]:u32 == low:u32(0x8244:u64)) & 
(mem_rl1:?u32[low:u32(0x81D0:u64),  e_little]:u32 == (low:u32(0x8140:u64) + (mem_rl1:?u32[low:u32(0x8138:u64),  e_little]:u32*low:u32(0x48:u64)))) & 
((mem_rl1:?u32[low:u32(0x8138:u64),  e_little]:u32 == low:u32(0x0:u64))|(mem_rl1:?u32[low:u32(0x8138:u64),  e_little]:u32 == low:u32(0x1:u64))) & 
(mem_rl1:?u32[low:u32(0x8124:u64),  e_little]:u32 == low:u32(0x8134:u64)) & 
((mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x808C:u64))|(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == low:u32(0x80D4:u64))) & 
(mem_rl1:?u32[low:u32(0x8120:u64),  e_little]:u32 == low:u32(0x82B0:u64)) & 
(mem_rl1:?u32[low:u32(0x811C:u64),  e_little]:u32 == (low:u32(0x808C:u64) + (mem_rl1:?u32[low:u32(0x8084:u64),  e_little]:u32*low:u32(0x48:u64)))) & 
((mem_rl1:?u32[low:u32(0x8084:u64),  e_little]:u32 == low:u32(0x0:u64))|(mem_rl1:?u32[low:u32(0x8084:u64),  e_little]:u32 == low:u32(0x1:u64))) & 
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
)

precondition:bool = ((
  loc_code_memory &
  hyper_invariants &
  my_precondition)
)


precondition:bool = (
  loc_code_memory &
  hyper_invariants &
  my_precondition
)

jmp "pc_0x18"




addr 0x0 @asm  "b +#3148"
label pc_0x0
PC:u32 = 0x0:u32
jmp  "pc_0xC4C"

addr 0x4 @asm  "b +#352"
label pc_0x4
PC:u32 = 0x4:u32
jmp  "pc_0x164"

addr 0x8 @asm  "b +#428"
label pc_0x8
PC:u32 = 0x8:u32
jmp  "pc_0x1B4"

addr 0xC @asm  "b +#168"
label pc_0xC
PC:u32 = 0xC:u32
jmp  "pc_0xB4"

addr 0x10 @asm  "b +#252"
label pc_0x10
PC:u32 = 0x10:u32
jmp  "pc_0x10C"

addr 0x14 @asm  "mov r0, r0"
label pc_0x14
PC:u32 = 0x14:u32
jmp  "pc_0x18"

addr 0x18 @asm  "b +#8"
label pc_0x18
PC:u32 = 0x18:u32
jmp  "pc_0x20"

addr 0x1C @asm  "b +#148"
label pc_0x1C
PC:u32 = 0x1C:u32
jmp  "pc_0xB0"


addr 0x20 @asm  "sub lr, lr, #4"
label pc_0x20
PC:u32 = 0x20:u32
tmp_lr_svc:u32 = (LR_SVC:u32 + low:u32(0xFFFFFFFC:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x24"

addr 0x24 @asm  "push {r0-r3}"
label pc_0x24
PC:u32 = 0x24:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF0:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =R3:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R2:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF4:u64)) ,e_little]:u32 =R1:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF0:u64)) ,e_little]:u32 =R0:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x28"

addr 0x28 @asm  "ldr r0, [pc, #472]"
label pc_0x28
PC:u32 = 0x28:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x1E0:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x2C"

addr 0x2C @asm  "ldr r1, [pc, #472]"
label pc_0x2C
PC:u32 = 0x2C:u32
tmp_r1:u32 = mem:?u32[(PC:u32 + low:u32(0x1E0:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x30"

addr 0x30 @asm  "ldr r2, [r0]"
label pc_0x30
PC:u32 = 0x30:u32
tmp_r2:u32 = mem:?u32[R0:u32,e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x34"

addr 0x34 @asm  "add r2, r2, #1"
label pc_0x34
PC:u32 = 0x34:u32
tmp_r2:u32 = (R2:u32 + low:u32(0x1:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0x38"

addr 0x38 @asm  "ldr r1, [r1, r2, lsl #2]"
label pc_0x38
PC:u32 = 0x38:u32
tmp_r1:u32 = mem:?u32[(R1:u32 + (R2:u32 << low:u32(0x2:u64))),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x3C"

addr 0x3C @asm  "str r2, [r0]"
label pc_0x3C
PC:u32 = 0x3C:u32
mem:?u32 = mem:?u32 with [R0:u32 ,e_little]:u32 =R2:u32
jmp  "pc_0x40"

addr 0x40 @asm  "str lr, [r1, #60]"
label pc_0x40
PC:u32 = 0x40:u32
mem:?u32 = mem:?u32 with [(R1:u32 + low:u32(0x3C:u64)) ,e_little]:u32 =LR_SVC:u32
jmp  "pc_0x44"

addr 0x44 @asm  "mov lr, r1"
label pc_0x44
PC:u32 = 0x44:u32
tmp_lr_svc:u32 = R1:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x48"

addr 0x48 @asm  "pop {r0-r3}"
label pc_0x48
PC:u32 = 0x48:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x10:u64))
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r2:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r1:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r0:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R0:u32 = tmp_r0:u32
R1:u32 = tmp_r1:u32
R2:u32 = tmp_r2:u32
R3:u32 = tmp_r3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x4C"

addr 0x4C @asm  "stmia lr, {r0-lr}^"
label pc_0x4C
PC:u32 = 0x4C:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x38:u64)) ,e_little]:u32 =LR:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x34:u64)) ,e_little]:u32 =SP:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x30:u64)) ,e_little]:u32 =R12:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x2C:u64)) ,e_little]:u32 =R11:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x28:u64)) ,e_little]:u32 =R10:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x24:u64)) ,e_little]:u32 =R9:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x20:u64)) ,e_little]:u32 =R8:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x1C:u64)) ,e_little]:u32 =R7:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x18:u64)) ,e_little]:u32 =R6:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x14:u64)) ,e_little]:u32 =R5:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x10:u64)) ,e_little]:u32 =R4:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0xC:u64)) ,e_little]:u32 =R3:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x8:u64)) ,e_little]:u32 =R2:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x4:u64)) ,e_little]:u32 =R1:u32
mem:?u32 = mem:?u32 with [LR_SVC:u32 ,e_little]:u32 =R0:u32
jmp  "pc_0x50"

addr 0x50 @asm  "mrs r12, spsr"
label pc_0x50
PC:u32 = 0x50:u32
tmp_r12:u32 = (((extend:u32(SVC_N_FLAG:bool) << 31:u32)& (0x1:u32 << 31:u32))|((extend:u32(SVC_Z_FLAG:bool) << 30:u32)& (0x1:u32 << 30:u32))|((extend:u32(SVC_C_FLAG:bool) << 29:u32)& (0x1:u32 << 29:u32))|((extend:u32(SVC_V_FLAG:bool) << 28:u32)& (0x1:u32 << 28:u32))|((extend:u32(SVC_Q_FLAG:bool) << 27:u32)& (0x1:u32 << 27:u32))|((extend:u32(SVC_J_FLAG:bool) << 24:u32)& (0x1:u32 << 24:u32))|((extend:u32(SVC_E_FLAG:bool) << 9:u32)& (0x1:u32 << 9:u32))|((extend:u32(SVC_A_FLAG:bool) << 8:u32)& (0x1:u32 << 8:u32))|((extend:u32(SVC_I_FLAG:bool) << 7:u32)& (0x1:u32 << 7:u32))|((extend:u32(SVC_F_FLAG:bool) << 6:u32)& (0x1:u32 << 6:u32))|((extend:u32(SVC_T_FLAG:bool) << 5:u32)& (0x1:u32 << 5:u32)))
R12:u32 = tmp_r12:u32
jmp  "pc_0x54"

addr 0x54 @asm  "str r12, [lr, #64]"
label pc_0x54
PC:u32 = 0x54:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x40:u64)) ,e_little]:u32 =R12:u32
jmp  "pc_0x58"

addr 0x58 @asm  "ldr r0, [pc, #432]"
label pc_0x58
PC:u32 = 0x58:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x1B8:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x5C"

addr 0x5C @asm  "ldr r1, [r0, #256]"
label pc_0x5C
PC:u32 = 0x5C:u32
tmp_r1:u32 = mem:?u32[(R0:u32 + low:u32(0x100:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x60"

addr 0x60 @asm  "mov lr, pc"
label pc_0x60
PC:u32 = 0x60:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x8:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x64"

addr 0x64 @asm  "bx r1"
label pc_0x64
PC:u32 = 0x64:u32
cjmp (R1<>0x00000780:u32), "lift_error", "pc_0x780"

jmp  ( if (R1:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*R1:u32)$/low:u32(0x2:u64)) else R1:u32)

addr 0x68 @asm  "ldr r0, [pc, #416]"
label pc_0x68
PC:u32 = 0x68:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x1A8:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x6C"

addr 0x6C @asm  "ldr r1, [r0, #264]"
label pc_0x6C
PC:u32 = 0x6C:u32
tmp_r1:u32 = mem:?u32[(R0:u32 + low:u32(0x108:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x70"

addr 0x70 @asm  "str r1, [r0, #304]"
label pc_0x70
PC:u32 = 0x70:u32
mem:?u32 = mem:?u32 with [(R0:u32 + low:u32(0x130:u64)) ,e_little]:u32 =R1:u32
jmp  "pc_0x74"

addr 0x74 @asm  "mov r2, #1"
label pc_0x74
PC:u32 = 0x74:u32
tmp_r2:u32 = low:u32(0x1:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x78"

addr 0x78 @asm  "mov r1, r2, lsl r1"
label pc_0x78
PC:u32 = 0x78:u32
tmp_r1:u32 = (R2:u32 << low:u32(extend:u64(R1:u32)))
R1:u32 = tmp_r1:u32
jmp  "pc_0x7C"

addr 0x7C @asm  "str r1, [r0, #292]"
label pc_0x7C
PC:u32 = 0x7C:u32
mem:?u32 = mem:?u32 with [(R0:u32 + low:u32(0x124:u64)) ,e_little]:u32 =R1:u32
jmp  "pc_0x80"

addr 0x80 @asm  "str r1, [r0, #288]"
label pc_0x80
PC:u32 = 0x80:u32
mem:?u32 = mem:?u32 with [(R0:u32 + low:u32(0x120:u64)) ,e_little]:u32 =R1:u32
jmp  "pc_0x84"


addr 0x84 @asm  "ldr r0, [pc, #380]"
label pc_0x84
PC:u32 = 0x84:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x184:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x88"

addr 0x88 @asm  "ldr r1, [pc, #380]"
label pc_0x88
PC:u32 = 0x88:u32
tmp_r1:u32 = mem:?u32[(PC:u32 + low:u32(0x184:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x8C"

addr 0x8C @asm  "ldr r2, [r0]"
label pc_0x8C
PC:u32 = 0x8C:u32
tmp_r2:u32 = mem:?u32[R0:u32,e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x90"

addr 0x90 @asm  "ldr lr, [r1, r2, lsl #2]"
label pc_0x90
PC:u32 = 0x90:u32
tmp_lr_svc:u32 = mem:?u32[(R1:u32 + (R2:u32 << low:u32(0x2:u64))),e_little]:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x94"

addr 0x94 @asm  "sub r2, r2, #1"
label pc_0x94
PC:u32 = 0x94:u32
tmp_r2:u32 = (R2:u32 + low:u32(0xFFFFFFFF:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0x98"

addr 0x98 @asm  "str r2, [r0]"
label pc_0x98
PC:u32 = 0x98:u32
mem:?u32 = mem:?u32 with [R0:u32 ,e_little]:u32 =R2:u32
jmp  "pc_0x9C"

addr 0x9C @asm  "ldr r0, [lr, #64]"
label pc_0x9C
PC:u32 = 0x9C:u32
tmp_r0:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x40:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xA0"

addr 0xA0 @asm  "msr spsr_fc, r0"
label pc_0xA0
PC:u32 = 0xA0:u32
tmp_svc_n_flag:bool = low:bool((R0:u32 & (0x1:u32 << (low:u32(0x1F:u64)))) >> low:u32(0x1F:u64))
tmp_svc_c_flag:bool = low:bool((R0:u32 & (0x1:u32 << (low:u32(0x1D:u64)))) >> low:u32(0x1D:u64))
tmp_svc_z_flag:bool = low:bool((R0:u32 & (0x1:u32 << (low:u32(0x1E:u64)))) >> low:u32(0x1E:u64))
tmp_svc_v_flag:bool = low:bool((R0:u32 & (0x1:u32 << (low:u32(0x1C:u64)))) >> low:u32(0x1C:u64))
tmp_svc_q_flag:bool = low:bool((R0:u32 & (0x1:u32 << (low:u32(0x1B:u64)))) >> low:u32(0x1B:u64))
SVC_N_FLAG:bool = tmp_svc_n_flag:bool
SVC_C_FLAG:bool = tmp_svc_c_flag:bool
SVC_Z_FLAG:bool = tmp_svc_z_flag:bool
SVC_V_FLAG:bool = tmp_svc_v_flag:bool
SVC_Q_FLAG:bool = tmp_svc_q_flag:bool
jmp  "pc_0xA4"

addr 0xA4 @asm  "ldmia lr, {r0-lr}^"
label pc_0xA4
PC:u32 = 0xA4:u32
tmp_lr:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x38:u64)),e_little]:u32
tmp_sp:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x34:u64)),e_little]:u32
tmp_r12:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x30:u64)),e_little]:u32
tmp_r11:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x2C:u64)),e_little]:u32
tmp_r10:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x28:u64)),e_little]:u32
tmp_r9:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x24:u64)),e_little]:u32
tmp_r8:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x20:u64)),e_little]:u32
tmp_r7:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x1C:u64)),e_little]:u32
tmp_r6:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x18:u64)),e_little]:u32
tmp_r5:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x14:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x10:u64)),e_little]:u32
tmp_r3:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r2:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r1:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r0:u32 = mem:?u32[LR_SVC:u32,e_little]:u32
R0:u32 = tmp_r0:u32
R1:u32 = tmp_r1:u32
R2:u32 = tmp_r2:u32
R3:u32 = tmp_r3:u32
R4:u32 = tmp_r4:u32
R5:u32 = tmp_r5:u32
R6:u32 = tmp_r6:u32
R7:u32 = tmp_r7:u32
R8:u32 = tmp_r8:u32
R9:u32 = tmp_r9:u32
R10:u32 = tmp_r10:u32
R11:u32 = tmp_r11:u32
R12:u32 = tmp_r12:u32
SP:u32 = tmp_sp:u32
LR:u32 = tmp_lr:u32
jmp  "pc_0xA8"

addr 0xA8 @asm  "ldr lr, [lr, #60]"
label pc_0xA8
PC:u32 = 0xA8:u32
tmp_lr_svc:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x3C:u64)),e_little]:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xAC"

addr 0xAC @asm  "movs pc, lr"
label pc_0xAC
PC:u32 = 0xAC:u32
tmp_n_flag:bool = low:bool(SVC_N_FLAG:bool)
tmp_c_flag:bool = low:bool(SVC_C_FLAG:bool)
tmp_z_flag:bool = low:bool(SVC_Z_FLAG:bool)
tmp_v_flag:bool = low:bool(SVC_V_FLAG:bool)
tmp_q_flag:bool = low:bool(SVC_Q_FLAG:bool)
tmp_e_flag:bool = low:bool(SVC_E_FLAG:bool)
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
Q_FLAG:bool = tmp_q_flag:bool
E_FLAG:bool = tmp_e_flag:bool


PC:u32=LR_SVC:u32
jmp "success"


jmp  ((low:u32(( if ~SVC_J_FLAG:bool & ~SVC_T_FLAG:bool then 0x4:u64 else 0x2:u64))*LR_SVC:u32)$/low:u32(( if ~SVC_J_FLAG:bool & ~SVC_T_FLAG:bool then 0x4:u64 else 0x2:u64)))


addr 0xB0 @asm  "b +#0"
label pc_0xB0
PC:u32 = 0xB0:u32
jmp  "pc_0xB0"


addr 0xB4 @asm  "sub lr, lr, #4"
label pc_0xB4
PC:u32 = 0xB4:u32
tmp_lr_svc:u32 = (LR_SVC:u32 + low:u32(0xFFFFFFFC:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xB8"

addr 0xB8 @asm  "push {r0-r3}"
label pc_0xB8
PC:u32 = 0xB8:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF0:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =R3:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R2:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF4:u64)) ,e_little]:u32 =R1:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF0:u64)) ,e_little]:u32 =R0:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xBC"

addr 0xBC @asm  "ldr r0, [pc, #324]"
label pc_0xBC
PC:u32 = 0xBC:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x14C:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xC0"

addr 0xC0 @asm  "ldr r1, [pc, #324]"
label pc_0xC0
PC:u32 = 0xC0:u32
tmp_r1:u32 = mem:?u32[(PC:u32 + low:u32(0x14C:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0xC4"

addr 0xC4 @asm  "ldr r2, [r0]"
label pc_0xC4
PC:u32 = 0xC4:u32
tmp_r2:u32 = mem:?u32[R0:u32,e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0xC8"

addr 0xC8 @asm  "add r2, r2, #1"
label pc_0xC8
PC:u32 = 0xC8:u32
tmp_r2:u32 = (R2:u32 + low:u32(0x1:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0xCC"

addr 0xCC @asm  "ldr r1, [r1, r2, lsl #2]"
label pc_0xCC
PC:u32 = 0xCC:u32
tmp_r1:u32 = mem:?u32[(R1:u32 + (R2:u32 << low:u32(0x2:u64))),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0xD0"

addr 0xD0 @asm  "str r2, [r0]"
label pc_0xD0
PC:u32 = 0xD0:u32
mem:?u32 = mem:?u32 with [R0:u32 ,e_little]:u32 =R2:u32
jmp  "pc_0xD4"

addr 0xD4 @asm  "str lr, [r1, #60]"
label pc_0xD4
PC:u32 = 0xD4:u32
mem:?u32 = mem:?u32 with [(R1:u32 + low:u32(0x3C:u64)) ,e_little]:u32 =LR_SVC:u32
jmp  "pc_0xD8"

addr 0xD8 @asm  "mov lr, r1"
label pc_0xD8
PC:u32 = 0xD8:u32
tmp_lr_svc:u32 = R1:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xDC"

addr 0xDC @asm  "pop {r0-r3}"
label pc_0xDC
PC:u32 = 0xDC:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x10:u64))
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r2:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r1:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r0:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R0:u32 = tmp_r0:u32
R1:u32 = tmp_r1:u32
R2:u32 = tmp_r2:u32
R3:u32 = tmp_r3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xE0"

addr 0xE0 @asm  "stmia lr, {r0-lr}^"
label pc_0xE0
PC:u32 = 0xE0:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x38:u64)) ,e_little]:u32 =LR:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x34:u64)) ,e_little]:u32 =SP:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x30:u64)) ,e_little]:u32 =R12:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x2C:u64)) ,e_little]:u32 =R11:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x28:u64)) ,e_little]:u32 =R10:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x24:u64)) ,e_little]:u32 =R9:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x20:u64)) ,e_little]:u32 =R8:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x1C:u64)) ,e_little]:u32 =R7:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x18:u64)) ,e_little]:u32 =R6:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x14:u64)) ,e_little]:u32 =R5:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x10:u64)) ,e_little]:u32 =R4:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0xC:u64)) ,e_little]:u32 =R3:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x8:u64)) ,e_little]:u32 =R2:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x4:u64)) ,e_little]:u32 =R1:u32
mem:?u32 = mem:?u32 with [LR_SVC:u32 ,e_little]:u32 =R0:u32
jmp  "pc_0xE4"

addr 0xE4 @asm  "mrs r12, spsr"
label pc_0xE4
PC:u32 = 0xE4:u32
tmp_r12:u32 = (((extend:u32(SVC_N_FLAG:bool) << 31:u32)& (0x1:u32 << 31:u32))|((extend:u32(SVC_Z_FLAG:bool) << 30:u32)& (0x1:u32 << 30:u32))|((extend:u32(SVC_C_FLAG:bool) << 29:u32)& (0x1:u32 << 29:u32))|((extend:u32(SVC_V_FLAG:bool) << 28:u32)& (0x1:u32 << 28:u32))|((extend:u32(SVC_Q_FLAG:bool) << 27:u32)& (0x1:u32 << 27:u32))|((extend:u32(SVC_J_FLAG:bool) << 24:u32)& (0x1:u32 << 24:u32))|((extend:u32(SVC_E_FLAG:bool) << 9:u32)& (0x1:u32 << 9:u32))|((extend:u32(SVC_A_FLAG:bool) << 8:u32)& (0x1:u32 << 8:u32))|((extend:u32(SVC_I_FLAG:bool) << 7:u32)& (0x1:u32 << 7:u32))|((extend:u32(SVC_F_FLAG:bool) << 6:u32)& (0x1:u32 << 6:u32))|((extend:u32(SVC_T_FLAG:bool) << 5:u32)& (0x1:u32 << 5:u32)))
R12:u32 = tmp_r12:u32
jmp  "pc_0xE8"

addr 0xE8 @asm  "str r12, [lr, #64]"
label pc_0xE8
PC:u32 = 0xE8:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x40:u64)) ,e_little]:u32 =R12:u32
jmp  "pc_0xEC"

addr 0xEC @asm  "ldr lr, [lr, #60]"
label pc_0xEC
PC:u32 = 0xEC:u32
tmp_lr_svc:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x3C:u64)),e_little]:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xF0"

addr 0xF0 @asm  "ldr r3, [pc, #284]"
label pc_0xF0
PC:u32 = 0xF0:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x124:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0xF4"

addr 0xF4 @asm  "ldr r3, [r3]"
label pc_0xF4
PC:u32 = 0xF4:u32
tmp_r3:u32 = mem:?u32[R3:u32,e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0xF8"

addr 0xF8 @asm  "mrc p15, #0, r0, c6, c0"
label pc_0xF8

jmp "lift_error"

addr 0xFC @asm  "mrc p15, #0, r1, c5, c0, #1"
label pc_0xFC

jmp "lift_error"

addr 0x100 @asm  "mov r2, lr"
label pc_0x100
PC:u32 = 0x100:u32
tmp_r2:u32 = LR_SVC:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x104"

addr 0x104 @asm  "ldr lr, [pc, #268]"
label pc_0x104
PC:u32 = 0x104:u32
tmp_lr_svc:u32 = mem:?u32[(PC:u32 + low:u32(0x114:u64)),e_little]:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x108"

addr 0x108 @asm  "bx r3"
label pc_0x108
PC:u32 = 0x108:u32
jmp  ( if (R3:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*R3:u32)$/low:u32(0x2:u64)) else R3:u32)


addr 0x10C @asm  "sub lr, lr, #8"
label pc_0x10C
PC:u32 = 0x10C:u32
tmp_lr_svc:u32 = (LR_SVC:u32 + low:u32(0xFFFFFFF8:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x110"

addr 0x110 @asm  "push {r0-r3}"
label pc_0x110
PC:u32 = 0x110:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF0:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =R3:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R2:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF4:u64)) ,e_little]:u32 =R1:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF0:u64)) ,e_little]:u32 =R0:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x114"

addr 0x114 @asm  "ldr r0, [pc, #236]"
label pc_0x114
PC:u32 = 0x114:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0xF4:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x118"

addr 0x118 @asm  "ldr r1, [pc, #236]"
label pc_0x118
PC:u32 = 0x118:u32
tmp_r1:u32 = mem:?u32[(PC:u32 + low:u32(0xF4:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x11C"

addr 0x11C @asm  "ldr r2, [r0]"
label pc_0x11C
PC:u32 = 0x11C:u32
tmp_r2:u32 = mem:?u32[R0:u32,e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x120"

addr 0x120 @asm  "add r2, r2, #1"
label pc_0x120
PC:u32 = 0x120:u32
tmp_r2:u32 = (R2:u32 + low:u32(0x1:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0x124"

addr 0x124 @asm  "ldr r1, [r1, r2, lsl #2]"
label pc_0x124
PC:u32 = 0x124:u32
tmp_r1:u32 = mem:?u32[(R1:u32 + (R2:u32 << low:u32(0x2:u64))),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x128"

addr 0x128 @asm  "str r2, [r0]"
label pc_0x128
PC:u32 = 0x128:u32
mem:?u32 = mem:?u32 with [R0:u32 ,e_little]:u32 =R2:u32
jmp  "pc_0x12C"

addr 0x12C @asm  "str lr, [r1, #60]"
label pc_0x12C
PC:u32 = 0x12C:u32
mem:?u32 = mem:?u32 with [(R1:u32 + low:u32(0x3C:u64)) ,e_little]:u32 =LR_SVC:u32
jmp  "pc_0x130"

addr 0x130 @asm  "mov lr, r1"
label pc_0x130
PC:u32 = 0x130:u32
tmp_lr_svc:u32 = R1:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x134"

addr 0x134 @asm  "pop {r0-r3}"
label pc_0x134
PC:u32 = 0x134:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x10:u64))
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r2:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r1:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r0:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R0:u32 = tmp_r0:u32
R1:u32 = tmp_r1:u32
R2:u32 = tmp_r2:u32
R3:u32 = tmp_r3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x138"

addr 0x138 @asm  "stmia lr, {r0-lr}^"
label pc_0x138
PC:u32 = 0x138:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x38:u64)) ,e_little]:u32 =LR:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x34:u64)) ,e_little]:u32 =SP:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x30:u64)) ,e_little]:u32 =R12:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x2C:u64)) ,e_little]:u32 =R11:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x28:u64)) ,e_little]:u32 =R10:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x24:u64)) ,e_little]:u32 =R9:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x20:u64)) ,e_little]:u32 =R8:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x1C:u64)) ,e_little]:u32 =R7:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x18:u64)) ,e_little]:u32 =R6:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x14:u64)) ,e_little]:u32 =R5:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x10:u64)) ,e_little]:u32 =R4:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0xC:u64)) ,e_little]:u32 =R3:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x8:u64)) ,e_little]:u32 =R2:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x4:u64)) ,e_little]:u32 =R1:u32
mem:?u32 = mem:?u32 with [LR_SVC:u32 ,e_little]:u32 =R0:u32
jmp  "pc_0x13C"

addr 0x13C @asm  "mrs r12, spsr"
label pc_0x13C
PC:u32 = 0x13C:u32
tmp_r12:u32 = (((extend:u32(SVC_N_FLAG:bool) << 31:u32)& (0x1:u32 << 31:u32))|((extend:u32(SVC_Z_FLAG:bool) << 30:u32)& (0x1:u32 << 30:u32))|((extend:u32(SVC_C_FLAG:bool) << 29:u32)& (0x1:u32 << 29:u32))|((extend:u32(SVC_V_FLAG:bool) << 28:u32)& (0x1:u32 << 28:u32))|((extend:u32(SVC_Q_FLAG:bool) << 27:u32)& (0x1:u32 << 27:u32))|((extend:u32(SVC_J_FLAG:bool) << 24:u32)& (0x1:u32 << 24:u32))|((extend:u32(SVC_E_FLAG:bool) << 9:u32)& (0x1:u32 << 9:u32))|((extend:u32(SVC_A_FLAG:bool) << 8:u32)& (0x1:u32 << 8:u32))|((extend:u32(SVC_I_FLAG:bool) << 7:u32)& (0x1:u32 << 7:u32))|((extend:u32(SVC_F_FLAG:bool) << 6:u32)& (0x1:u32 << 6:u32))|((extend:u32(SVC_T_FLAG:bool) << 5:u32)& (0x1:u32 << 5:u32)))
R12:u32 = tmp_r12:u32
jmp  "pc_0x140"

addr 0x140 @asm  "str r12, [lr, #64]"
label pc_0x140
PC:u32 = 0x140:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x40:u64)) ,e_little]:u32 =R12:u32
jmp  "pc_0x144"

addr 0x144 @asm  "ldr lr, [lr, #60]"
label pc_0x144
PC:u32 = 0x144:u32
tmp_lr_svc:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x3C:u64)),e_little]:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x148"

addr 0x148 @asm  "ldr r3, [pc, #204]"
label pc_0x148
PC:u32 = 0x148:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0xD4:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x14C"

addr 0x14C @asm  "ldr r3, [r3]"
label pc_0x14C
PC:u32 = 0x14C:u32
tmp_r3:u32 = mem:?u32[R3:u32,e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x150"

addr 0x150 @asm  "mrc p15, #0, r0, c6, c0"
label pc_0x150

jmp "lift_error"

addr 0x154 @asm  "mrc p15, #0, r1, c5, c0"
label pc_0x154

jmp "lift_error"

addr 0x158 @asm  "mov r2, lr"
label pc_0x158
PC:u32 = 0x158:u32
tmp_r2:u32 = LR_SVC:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x15C"

addr 0x15C @asm  "ldr lr, [pc, #180]"
label pc_0x15C
PC:u32 = 0x15C:u32
tmp_lr_svc:u32 = mem:?u32[(PC:u32 + low:u32(0xBC:u64)),e_little]:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x160"

addr 0x160 @asm  "bx r3"
label pc_0x160
PC:u32 = 0x160:u32
jmp  ( if (R3:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*R3:u32)$/low:u32(0x2:u64)) else R3:u32)


addr 0x164 @asm  "push {r0-r3}"
label pc_0x164
PC:u32 = 0x164:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF0:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =R3:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R2:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF4:u64)) ,e_little]:u32 =R1:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF0:u64)) ,e_little]:u32 =R0:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x168"

addr 0x168 @asm  "ldr r0, [pc, #152]"
label pc_0x168
PC:u32 = 0x168:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0xA0:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x16C"

addr 0x16C @asm  "ldr r1, [pc, #152]"
label pc_0x16C
PC:u32 = 0x16C:u32
tmp_r1:u32 = mem:?u32[(PC:u32 + low:u32(0xA0:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x170"

addr 0x170 @asm  "ldr r2, [r0]"
label pc_0x170
PC:u32 = 0x170:u32
tmp_r2:u32 = mem:?u32[R0:u32,e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x174"

addr 0x174 @asm  "add r2, r2, #1"
label pc_0x174
PC:u32 = 0x174:u32
tmp_r2:u32 = (R2:u32 + low:u32(0x1:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0x178"

addr 0x178 @asm  "ldr r1, [r1, r2, lsl #2]"
label pc_0x178
PC:u32 = 0x178:u32
tmp_r1:u32 = mem:?u32[(R1:u32 + (R2:u32 << low:u32(0x2:u64))),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x17C"

addr 0x17C @asm  "str r2, [r0]"
label pc_0x17C
PC:u32 = 0x17C:u32
mem:?u32 = mem:?u32 with [R0:u32 ,e_little]:u32 =R2:u32
jmp  "pc_0x180"

addr 0x180 @asm  "str lr, [r1, #60]"
label pc_0x180
PC:u32 = 0x180:u32
mem:?u32 = mem:?u32 with [(R1:u32 + low:u32(0x3C:u64)) ,e_little]:u32 =LR_SVC:u32
jmp  "pc_0x184"

addr 0x184 @asm  "mov lr, r1"
label pc_0x184
PC:u32 = 0x184:u32
tmp_lr_svc:u32 = R1:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x188"

addr 0x188 @asm  "pop {r0-r3}"
label pc_0x188
PC:u32 = 0x188:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x10:u64))
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r2:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r1:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r0:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R0:u32 = tmp_r0:u32
R1:u32 = tmp_r1:u32
R2:u32 = tmp_r2:u32
R3:u32 = tmp_r3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x18C"

addr 0x18C @asm  "stmia lr, {r0-lr}^"
label pc_0x18C
PC:u32 = 0x18C:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x38:u64)) ,e_little]:u32 =LR:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x34:u64)) ,e_little]:u32 =SP:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x30:u64)) ,e_little]:u32 =R12:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x2C:u64)) ,e_little]:u32 =R11:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x28:u64)) ,e_little]:u32 =R10:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x24:u64)) ,e_little]:u32 =R9:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x20:u64)) ,e_little]:u32 =R8:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x1C:u64)) ,e_little]:u32 =R7:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x18:u64)) ,e_little]:u32 =R6:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x14:u64)) ,e_little]:u32 =R5:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x10:u64)) ,e_little]:u32 =R4:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0xC:u64)) ,e_little]:u32 =R3:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x8:u64)) ,e_little]:u32 =R2:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x4:u64)) ,e_little]:u32 =R1:u32
mem:?u32 = mem:?u32 with [LR_SVC:u32 ,e_little]:u32 =R0:u32
jmp  "pc_0x190"

addr 0x190 @asm  "mrs r12, spsr"
label pc_0x190
PC:u32 = 0x190:u32
tmp_r12:u32 = (((extend:u32(SVC_N_FLAG:bool) << 31:u32)& (0x1:u32 << 31:u32))|((extend:u32(SVC_Z_FLAG:bool) << 30:u32)& (0x1:u32 << 30:u32))|((extend:u32(SVC_C_FLAG:bool) << 29:u32)& (0x1:u32 << 29:u32))|((extend:u32(SVC_V_FLAG:bool) << 28:u32)& (0x1:u32 << 28:u32))|((extend:u32(SVC_Q_FLAG:bool) << 27:u32)& (0x1:u32 << 27:u32))|((extend:u32(SVC_J_FLAG:bool) << 24:u32)& (0x1:u32 << 24:u32))|((extend:u32(SVC_E_FLAG:bool) << 9:u32)& (0x1:u32 << 9:u32))|((extend:u32(SVC_A_FLAG:bool) << 8:u32)& (0x1:u32 << 8:u32))|((extend:u32(SVC_I_FLAG:bool) << 7:u32)& (0x1:u32 << 7:u32))|((extend:u32(SVC_F_FLAG:bool) << 6:u32)& (0x1:u32 << 6:u32))|((extend:u32(SVC_T_FLAG:bool) << 5:u32)& (0x1:u32 << 5:u32)))
R12:u32 = tmp_r12:u32
jmp  "pc_0x194"

addr 0x194 @asm  "str r12, [lr, #64]"
label pc_0x194
PC:u32 = 0x194:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x40:u64)) ,e_little]:u32 =R12:u32
jmp  "pc_0x198"

addr 0x198 @asm  "ldr lr, [lr, #60]"
label pc_0x198
PC:u32 = 0x198:u32
tmp_lr_svc:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x3C:u64)),e_little]:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x19C"

addr 0x19C @asm  "ldr r3, [pc, #124]"
label pc_0x19C
PC:u32 = 0x19C:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x84:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x1A0"

addr 0x1A0 @asm  "ldr r3, [r3]"
label pc_0x1A0
PC:u32 = 0x1A0:u32
tmp_r3:u32 = mem:?u32[R3:u32,e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x1A4"

addr 0x1A4 @asm  "sub r2, lr, #4"
label pc_0x1A4
PC:u32 = 0x1A4:u32
tmp_r2:u32 = (LR_SVC:u32 + low:u32(0xFFFFFFFC:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0x1A8"

addr 0x1A8 @asm  "ldr r0, [r2]"
label pc_0x1A8
PC:u32 = 0x1A8:u32
tmp_r0:u32 = mem:?u32[R2:u32,e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x1AC"

addr 0x1AC @asm  "ldr lr, [pc, #100]"
label pc_0x1AC
PC:u32 = 0x1AC:u32
tmp_lr_svc:u32 = mem:?u32[(PC:u32 + low:u32(0x6C:u64)),e_little]:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x1B0"

addr 0x1B0 @asm  "bx r3"
label pc_0x1B0
PC:u32 = 0x1B0:u32
jmp  ( if (R3:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*R3:u32)$/low:u32(0x2:u64)) else R3:u32)


addr 0x1B4 @asm  "push {r0-r3}"
label pc_0x1B4
PC:u32 = 0x1B4:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF0:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =R3:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R2:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF4:u64)) ,e_little]:u32 =R1:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF0:u64)) ,e_little]:u32 =R0:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x1B8"

addr 0x1B8 @asm  "ldr r0, [pc, #72]"
label pc_0x1B8
PC:u32 = 0x1B8:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x50:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x1BC"

addr 0x1BC @asm  "ldr r1, [pc, #72]"
label pc_0x1BC
PC:u32 = 0x1BC:u32
tmp_r1:u32 = mem:?u32[(PC:u32 + low:u32(0x50:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x1C0"

addr 0x1C0 @asm  "ldr r2, [r0]"
label pc_0x1C0
PC:u32 = 0x1C0:u32
tmp_r2:u32 = mem:?u32[R0:u32,e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x1C4"

addr 0x1C4 @asm  "add r2, r2, #1"
label pc_0x1C4
PC:u32 = 0x1C4:u32
tmp_r2:u32 = (R2:u32 + low:u32(0x1:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0x1C8"

addr 0x1C8 @asm  "ldr r1, [r1, r2, lsl #2]"
label pc_0x1C8
PC:u32 = 0x1C8:u32
tmp_r1:u32 = mem:?u32[(R1:u32 + (R2:u32 << low:u32(0x2:u64))),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x1CC"

addr 0x1CC @asm  "str r2, [r0]"
label pc_0x1CC
PC:u32 = 0x1CC:u32
mem:?u32 = mem:?u32 with [R0:u32 ,e_little]:u32 =R2:u32
jmp  "pc_0x1D0"

addr 0x1D0 @asm  "str lr, [r1, #60]"
label pc_0x1D0
PC:u32 = 0x1D0:u32
mem:?u32 = mem:?u32 with [(R1:u32 + low:u32(0x3C:u64)) ,e_little]:u32 =LR_SVC:u32
jmp  "pc_0x1D4"

addr 0x1D4 @asm  "mov lr, r1"
label pc_0x1D4
PC:u32 = 0x1D4:u32
tmp_lr_svc:u32 = R1:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x1D8"

addr 0x1D8 @asm  "pop {r0-r3}"
label pc_0x1D8
PC:u32 = 0x1D8:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x10:u64))
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r2:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r1:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r0:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R0:u32 = tmp_r0:u32
R1:u32 = tmp_r1:u32
R2:u32 = tmp_r2:u32
R3:u32 = tmp_r3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x1DC"

addr 0x1DC @asm  "stmia lr, {r0-lr}^"
label pc_0x1DC
PC:u32 = 0x1DC:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x38:u64)) ,e_little]:u32 =LR:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x34:u64)) ,e_little]:u32 =SP:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x30:u64)) ,e_little]:u32 =R12:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x2C:u64)) ,e_little]:u32 =R11:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x28:u64)) ,e_little]:u32 =R10:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x24:u64)) ,e_little]:u32 =R9:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x20:u64)) ,e_little]:u32 =R8:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x1C:u64)) ,e_little]:u32 =R7:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x18:u64)) ,e_little]:u32 =R6:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x14:u64)) ,e_little]:u32 =R5:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x10:u64)) ,e_little]:u32 =R4:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0xC:u64)) ,e_little]:u32 =R3:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x8:u64)) ,e_little]:u32 =R2:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x4:u64)) ,e_little]:u32 =R1:u32
mem:?u32 = mem:?u32 with [LR_SVC:u32 ,e_little]:u32 =R0:u32
jmp  "pc_0x1E0"

addr 0x1E0 @asm  "mrs r12, spsr"
label pc_0x1E0
PC:u32 = 0x1E0:u32
tmp_r12:u32 = (((extend:u32(SVC_N_FLAG:bool) << 31:u32)& (0x1:u32 << 31:u32))|((extend:u32(SVC_Z_FLAG:bool) << 30:u32)& (0x1:u32 << 30:u32))|((extend:u32(SVC_C_FLAG:bool) << 29:u32)& (0x1:u32 << 29:u32))|((extend:u32(SVC_V_FLAG:bool) << 28:u32)& (0x1:u32 << 28:u32))|((extend:u32(SVC_Q_FLAG:bool) << 27:u32)& (0x1:u32 << 27:u32))|((extend:u32(SVC_J_FLAG:bool) << 24:u32)& (0x1:u32 << 24:u32))|((extend:u32(SVC_E_FLAG:bool) << 9:u32)& (0x1:u32 << 9:u32))|((extend:u32(SVC_A_FLAG:bool) << 8:u32)& (0x1:u32 << 8:u32))|((extend:u32(SVC_I_FLAG:bool) << 7:u32)& (0x1:u32 << 7:u32))|((extend:u32(SVC_F_FLAG:bool) << 6:u32)& (0x1:u32 << 6:u32))|((extend:u32(SVC_T_FLAG:bool) << 5:u32)& (0x1:u32 << 5:u32)))
R12:u32 = tmp_r12:u32
jmp  "pc_0x1E4"

addr 0x1E4 @asm  "str r12, [lr, #64]"
label pc_0x1E4
PC:u32 = 0x1E4:u32
mem:?u32 = mem:?u32 with [(LR_SVC:u32 + low:u32(0x40:u64)) ,e_little]:u32 =R12:u32
jmp  "pc_0x1E8"

addr 0x1E8 @asm  "ldr lr, [lr, #60]"
label pc_0x1E8
PC:u32 = 0x1E8:u32
tmp_lr_svc:u32 = mem:?u32[(LR_SVC:u32 + low:u32(0x3C:u64)),e_little]:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x1EC"

addr 0x1EC @asm  "ldr r12, [pc, #48]"
label pc_0x1EC
PC:u32 = 0x1EC:u32
tmp_r12:u32 = mem:?u32[(PC:u32 + low:u32(0x38:u64)),e_little]:u32
R12:u32 = tmp_r12:u32
jmp  "pc_0x1F0"

addr 0x1F0 @asm  "ldr r12, [r12]"
label pc_0x1F0
PC:u32 = 0x1F0:u32
tmp_r12:u32 = mem:?u32[R12:u32,e_little]:u32
R12:u32 = tmp_r12:u32
jmp  "pc_0x1F4"

addr 0x1F4 @asm  "sub r11, lr, #4"
label pc_0x1F4
PC:u32 = 0x1F4:u32
tmp_r11:u32 = (LR_SVC:u32 + low:u32(0xFFFFFFFC:u64))
R11:u32 = tmp_r11:u32
jmp  "pc_0x1F8"

addr 0x1F8 @asm  "ldr r2, [r11]"
label pc_0x1F8
PC:u32 = 0x1F8:u32
tmp_r2:u32 = mem:?u32[R11:u32,e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x1FC"

addr 0x1FC @asm  "bic r2, r2, #0xFF000000"
label pc_0x1FC
PC:u32 = 0x1FC:u32
tmp_r2:u32 = (R2:u32 & low:u32(0xFFFFFF:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0x200"

addr 0x200 @asm  "ldr lr, [pc, #16]"
label pc_0x200
PC:u32 = 0x200:u32
tmp_lr_svc:u32 = mem:?u32[(PC:u32 + low:u32(0x18:u64)),e_little]:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x204"

addr 0x204 @asm  "bx r12"
label pc_0x204
PC:u32 = 0x204:u32
jmp  R12

addr 0x208 @asm  "andeq r8, r0, r12, lsl r3"
label pc_0x208
PC:u32 = 0x208:u32
TmpV_1:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_1:bool , "L_1" , "pc_0x20C"
label L_1
tmp_r8:u32 = (R0:u32 & (R12:u32 << low:u32(extend:u64(R3:u32))))
R8:u32 = tmp_r8:u32
jmp  "pc_0x20C"

addr 0x20C @asm  "andeq r8, r0, r0, lsr #6"
label pc_0x20C
PC:u32 = 0x20C:u32
TmpV_2:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_2:bool , "L_3" , "pc_0x210"
label L_3
tmp_r8:u32 = (R0:u32 & (R0:u32 >> low:u32(0x6:u64)))
R8:u32 = tmp_r8:u32
jmp  "pc_0x210"

addr 0x210 @asm  "WORD 0xF6000010"
label pc_0x210

jmp "lift_error"

addr 0x214 @asm  "andeq r2, r0, r0"
label pc_0x214
PC:u32 = 0x214:u32
TmpV_3:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_3:bool , "L_5" , "pc_0x218"
label L_5
tmp_r2:u32 = R0:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x218"

addr 0x218 @asm  "andeq r0, r0, r4, lsl #1"
label pc_0x218
PC:u32 = 0x218:u32
TmpV_4:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_4:bool , "L_7" , "pc_0x21C"
label L_7
tmp_r0:u32 = (R0:u32 & (R4:u32 << low:u32(0x1:u64)))
R0:u32 = tmp_r0:u32
jmp  "pc_0x21C"

addr 0x21C @asm  "andeq r2, r0, r4"
label pc_0x21C
PC:u32 = 0x21C:u32
TmpV_5:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_5:bool , "L_9" , "pc_0x220"
label L_9
tmp_r2:u32 = (R0:u32 & R4:u32)
R2:u32 = tmp_r2:u32
jmp  "pc_0x220"

addr 0x220 @asm  "andeq r2, r0, r12"
label pc_0x220
PC:u32 = 0x220:u32
TmpV_6:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_6:bool , "L_11" , "pc_0x224"
label L_11
tmp_r2:u32 = (R0:u32 & R12:u32)
R2:u32 = tmp_r2:u32
jmp  "pc_0x224"

addr 0x224 @asm  "andeq r2, r0, r8"
label pc_0x224
PC:u32 = 0x224:u32
TmpV_7:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_7:bool , "L_13" , "pc_0x228"
label L_13
tmp_r2:u32 = (R0:u32 & R8:u32)
R2:u32 = tmp_r2:u32
jmp  "pc_0x228"


addr 0x228 @asm  "ldr r0, [pc, #56]"
label pc_0x228
PC:u32 = 0x228:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x40:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x22C"

addr 0x22C @asm  "add r1, r0, #4"
label pc_0x22C
PC:u32 = 0x22C:u32
tmp_r1:u32 = (R0:u32 + low:u32(0x4:u64))
R1:u32 = tmp_r1:u32
jmp  "pc_0x230"

addr 0x230 @asm  "ldr r0, [r0]"
label pc_0x230
PC:u32 = 0x230:u32
tmp_r0:u32 = mem:?u32[R0:u32,e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x234"

addr 0x234 @asm  "ldr r0, [r1, r0, lsl #2]"
label pc_0x234
PC:u32 = 0x234:u32
tmp_r0:u32 = mem:?u32[(R1:u32 + (R0:u32 << low:u32(0x2:u64))),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x238"

addr 0x238 @asm  "bx lr"
label pc_0x238
PC:u32 = 0x238:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x23C @asm  "ldr r1, [pc, #36]"
label pc_0x23C
PC:u32 = 0x23C:u32
tmp_r1:u32 = mem:?u32[(PC:u32 + low:u32(0x2C:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x240"

addr 0x240 @asm  "add r2, r1, #4"
label pc_0x240
PC:u32 = 0x240:u32
tmp_r2:u32 = (R1:u32 + low:u32(0x4:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0x244"

addr 0x244 @asm  "ldr r1, [r1]"
label pc_0x244
PC:u32 = 0x244:u32
tmp_r1:u32 = mem:?u32[R1:u32,e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x248"

addr 0x248 @asm  "str r0, [r2, r1, lsl #2]"
label pc_0x248
PC:u32 = 0x248:u32
mem:?u32 = mem:?u32 with [(R2:u32 + (R1:u32 << low:u32(0x2:u64))) ,e_little]:u32 =R0:u32
jmp  "pc_0x24C"

addr 0x24C @asm  "bx lr"
label pc_0x24C
PC:u32 = 0x24C:u32
cjmp (LR_SVC<>0x888:u32), "lift_error", "pc_0x888"

jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x250 @asm  "ldr r2, [pc, #20]"
label pc_0x250
PC:u32 = 0x250:u32
tmp_r2:u32 = mem:?u32[(PC:u32 + low:u32(0x1C:u64)),e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x254"

addr 0x254 @asm  "str r0, [r2, #4]"
label pc_0x254
PC:u32 = 0x254:u32
mem:?u32 = mem:?u32 with [(R2:u32 + low:u32(0x4:u64)) ,e_little]:u32 =R0:u32
jmp  "pc_0x258"

addr 0x258 @asm  "bx lr"
label pc_0x258
PC:u32 = 0x258:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x25C @asm  "ldr r0, [pc, #4]"
label pc_0x25C
PC:u32 = 0x25C:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0xC:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x260"

addr 0x260 @asm  "ldr r0, [r0]"
label pc_0x260
PC:u32 = 0x260:u32
tmp_r0:u32 = mem:?u32[R0:u32,e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x264"

addr 0x264 @asm  "bx lr"
label pc_0x264
PC:u32 = 0x264:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x268 @asm  "andeq r8, r0, r12, lsl r3"
label pc_0x268
PC:u32 = 0x268:u32
TmpV_8:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_8:bool , "L_15" , "pc_0x26C"
label L_15
tmp_r8:u32 = (R0:u32 & (R12:u32 << low:u32(extend:u64(R3:u32))))
R8:u32 = tmp_r8:u32
jmp  "pc_0x26C"

addr 0x26C @asm  "andeq r8, r0, r0, lsr #6"
label pc_0x26C
PC:u32 = 0x26C:u32
TmpV_9:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_9:bool , "L_17" , "pc_0x270"
label L_17
tmp_r8:u32 = (R0:u32 & (R0:u32 >> low:u32(0x6:u64)))
R8:u32 = tmp_r8:u32
jmp  "pc_0x270"


addr 0x270 @asm  "mov r3, #0"
label pc_0x270
PC:u32 = 0x270:u32
tmp_r3:u32 = low:u32(0x0:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x274"

addr 0x274 @asm  "strb r3, [r0]"
label pc_0x274
PC:u32 = 0x274:u32
mem:?u32 = mem:?u32 with [R0:u32 ,e_little]:u8 = (low:u8(R3:u32))jmp  "pc_0x278"

addr 0x278 @asm  "strb r3, [r1]"
label pc_0x278
PC:u32 = 0x278:u32
mem:?u32 = mem:?u32 with [R1:u32 ,e_little]:u8 = (low:u8(R3:u32))jmp  "pc_0x27C"

addr 0x27C @asm  "mov pc, lr"
label pc_0x27C
PC:u32 = 0x27C:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x280 @asm  "ldr r3, [pc, #4]"
label pc_0x280
PC:u32 = 0x280:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0xC:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x284"

addr 0x284 @asm  "stmia r3, {r0, r1}"
label pc_0x284
PC:u32 = 0x284:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x4:u64)) ,e_little]:u32 =R1:u32
mem:?u32 = mem:?u32 with [R3:u32 ,e_little]:u32 =R0:u32
jmp  "pc_0x288"

addr 0x288 @asm  "mov pc, lr"
label pc_0x288
PC:u32 = 0x288:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x28C @asm  "andeq r2, r0, r0"
label pc_0x28C
PC:u32 = 0x28C:u32
TmpV_10:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_10:bool , "L_19" , "pc_0x290"
label L_19
tmp_r2:u32 = R0:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x290"


addr 0x290 @asm  "ldr r3, [pc, #4]"
label pc_0x290
PC:u32 = 0x290:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0xC:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x294"

addr 0x294 @asm  "str r0, [r3, #8]"
label pc_0x294
PC:u32 = 0x294:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x8:u64)) ,e_little]:u32 =R0:u32
jmp  "pc_0x298"

addr 0x298 @asm  "mov pc, lr"
label pc_0x298
PC:u32 = 0x298:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x29C @asm  "andeq r2, r0, r0"
label pc_0x29C
PC:u32 = 0x29C:u32
TmpV_11:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_11:bool , "L_21" , "pc_0x2A0"
label L_21
tmp_r2:u32 = R0:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x2A0"


addr 0x2A0 @asm  "ldr r3, [pc, #4]"
label pc_0x2A0
PC:u32 = 0x2A0:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0xC:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x2A4"

addr 0x2A4 @asm  "str r0, [r3, #12]"
label pc_0x2A4
PC:u32 = 0x2A4:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xC:u64)) ,e_little]:u32 =R0:u32
jmp  "pc_0x2A8"

addr 0x2A8 @asm  "mov pc, lr"
label pc_0x2A8
PC:u32 = 0x2A8:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x2AC @asm  "andeq r2, r0, r0"
label pc_0x2AC
PC:u32 = 0x2AC:u32
TmpV_12:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_12:bool , "L_23" , "pc_0x2B0"
label L_23
tmp_r2:u32 = R0:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x2B0"


addr 0x2B0 @asm  "mov pc, lr"
label pc_0x2B0
PC:u32 = 0x2B0:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x2B4 @asm  "mov r0, #1"
label pc_0x2B4
PC:u32 = 0x2B4:u32
tmp_r0:u32 = low:u32(0x1:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x2B8"

addr 0x2B8 @asm  "mov r1, r0"
label pc_0x2B8
PC:u32 = 0x2B8:u32
tmp_r1:u32 = R0:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x2BC"

addr 0x2BC @asm  "mov r2, r0"
label pc_0x2BC
PC:u32 = 0x2BC:u32
tmp_r2:u32 = R0:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x2C0"

addr 0x2C0 @asm  "push {r4, lr}"
label pc_0x2C0
PC:u32 = 0x2C0:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF8:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R4:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x2C4"

addr 0x2C4 @asm  "bl +#180"
label pc_0x2C4
PC:u32 = 0x2C4:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x378"

addr 0x2C8 @asm  "mov r0, #1"
label pc_0x2C8
PC:u32 = 0x2C8:u32
tmp_r0:u32 = low:u32(0x1:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x2CC"

addr 0x2CC @asm  "bl +#148"
label pc_0x2CC
PC:u32 = 0x2CC:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x360"

addr 0x2D0 @asm  "mov r0, #0"
label pc_0x2D0
PC:u32 = 0x2D0:u32
tmp_r0:u32 = low:u32(0x0:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x2D4"

addr 0x2D4 @asm  "pop {r4, lr}"
label pc_0x2D4
PC:u32 = 0x2D4:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x8:u64))
tmp_lr_svc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R4:u32 = tmp_r4:u32
SP_SVC:u32 = tmp_sp_svc:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x2D8"

addr 0x2D8 @asm  "b +#2560"
label pc_0x2D8
PC:u32 = 0x2D8:u32
jmp  "pc_0xCD8"


addr 0x2DC @asm  "subs r0, r0, #0"
label pc_0x2DC
PC:u32 = 0x2DC:u32
tmp_n_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x2E0"

addr 0x2E0 @asm  "movne r0, #1"
label pc_0x2E0
PC:u32 = 0x2E0:u32
TmpV_13:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_13:bool , "L_25" , "pc_0x2E4"
label L_25
tmp_r0:u32 = low:u32(0x1:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x2E4"

addr 0x2E4 @asm  "subs r1, r1, #0"
label pc_0x2E4
PC:u32 = 0x2E4:u32
tmp_n_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R1:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x2E8"

addr 0x2E8 @asm  "movne r1, #1"
label pc_0x2E8
PC:u32 = 0x2E8:u32
TmpV_14:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_14:bool , "L_27" , "pc_0x2EC"
label L_27
tmp_r1:u32 = low:u32(0x1:u64)
R1:u32 = tmp_r1:u32
jmp  "pc_0x2EC"

addr 0x2EC @asm  "ands r3, r1, r0"
label pc_0x2EC
PC:u32 = 0x2EC:u32
tmp_r3:u32 = (R1:u32 & R0:u32)
tmp_n_flag:bool = low:bool(low:bool(((R1:u32 & R0:u32)) >> 0x1f:u32 ))
tmp_z_flag:bool = low:bool(((R1:u32 & R0:u32) == low:u32(0x0:u64)))
R3:u32 = tmp_r3:u32
N_FLAG:bool = tmp_n_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
jmp  "pc_0x2F0"

addr 0x2F0 @asm  "beq +#16"
label pc_0x2F0
PC:u32 = 0x2F0:u32
TmpV_15:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_15:bool , "pc_0x300" , "pc_0x2F4"

addr 0x2F4 @asm  "mov r3, #0"
label pc_0x2F4
PC:u32 = 0x2F4:u32
tmp_r3:u32 = low:u32(0x0:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x2F8"

addr 0x2F8 @asm  "mcr p15, #0, r3, c8, c7"
label pc_0x2F8

jmp "lift_error"

addr 0x2FC @asm  "mov pc, lr"
label pc_0x2FC
PC:u32 = 0x2FC:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x300 @asm  "cmp r0, #0"
label pc_0x300
PC:u32 = 0x300:u32
tmp_n_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x304"

addr 0x304 @asm  "beq +#12"
label pc_0x304
PC:u32 = 0x304:u32
TmpV_16:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_16:bool , "pc_0x310" , "pc_0x308"

addr 0x308 @asm  "mcr p15, #0, r3, c8, c5"
label pc_0x308

jmp "lift_error"

addr 0x30C @asm  "mov pc, lr"
label pc_0x30C
PC:u32 = 0x30C:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x310 @asm  "cmp r1, #0"
label pc_0x310
PC:u32 = 0x310:u32
tmp_n_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R1:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x314"

addr 0x314 @asm  "moveq pc, lr"
label pc_0x314
PC:u32 = 0x314:u32
jmp "lift_error"
cjmp TmpV_17:bool , ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32) , "pc_0x318"

addr 0x318 @asm  "mcr p15, #0, r0, c8, c6"
label pc_0x318

jmp "lift_error"

addr 0x31C @asm  "mov pc, lr"
label pc_0x31C
PC:u32 = 0x31C:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x320 @asm  "subs r0, r0, #0"
label pc_0x320
PC:u32 = 0x320:u32
tmp_n_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x324"

addr 0x324 @asm  "movne r0, #1"
label pc_0x324
PC:u32 = 0x324:u32
TmpV_18:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_18:bool , "L_35" , "pc_0x328"
label L_35
tmp_r0:u32 = low:u32(0x1:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x328"

addr 0x328 @asm  "subs r1, r1, #0"
label pc_0x328
PC:u32 = 0x328:u32
tmp_n_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R1:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x32C"

addr 0x32C @asm  "movne r1, #1"
label pc_0x32C
PC:u32 = 0x32C:u32
TmpV_19:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_19:bool , "L_37" , "pc_0x330"
label L_37
tmp_r1:u32 = low:u32(0x1:u64)
R1:u32 = tmp_r1:u32
jmp  "pc_0x330"

addr 0x330 @asm  "tst r1, r0"
label pc_0x330
PC:u32 = 0x330:u32
tmp_n_flag:bool = low:bool(low:bool(((R1:u32 & R0:u32)) >> 0x1f:u32 ))
tmp_z_flag:bool = low:bool(((R1:u32 & R0:u32) == low:u32(0x0:u64)))
N_FLAG:bool = tmp_n_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
jmp  "pc_0x334"

addr 0x334 @asm  "beq +#12"
label pc_0x334
PC:u32 = 0x334:u32
TmpV_20:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_20:bool , "pc_0x340" , "pc_0x338"

addr 0x338 @asm  "mcr p15, #0, r2, c8, c7, #1"
label pc_0x338

jmp "lift_error"

addr 0x33C @asm  "mov pc, lr"
label pc_0x33C
PC:u32 = 0x33C:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x340 @asm  "cmp r0, #0"
label pc_0x340
PC:u32 = 0x340:u32
tmp_n_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x344"

addr 0x344 @asm  "beq +#12"
label pc_0x344
PC:u32 = 0x344:u32
TmpV_21:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_21:bool , "pc_0x350" , "pc_0x348"

addr 0x348 @asm  "mcr p15, #0, r2, c8, c5, #1"
label pc_0x348

jmp "lift_error"

addr 0x34C @asm  "mov pc, lr"
label pc_0x34C
PC:u32 = 0x34C:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x350 @asm  "cmp r1, #0"
label pc_0x350
PC:u32 = 0x350:u32
tmp_n_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R1:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x354"

addr 0x354 @asm  "moveq pc, lr"
label pc_0x354
PC:u32 = 0x354:u32
jmp "lift_error"
cjmp TmpV_22:bool , ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32) , "pc_0x358"

addr 0x358 @asm  "mcr p15, #0, r2, c8, c6, #1"
label pc_0x358

jmp "lift_error"

addr 0x35C @asm  "mov pc, lr"
label pc_0x35C
PC:u32 = 0x35C:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x360 @asm  "mrc p15, #0, r3, c1, c0"
label pc_0x360

jmp "lift_error"

addr 0x364 @asm  "cmp r0, #0"
label pc_0x364
PC:u32 = 0x364:u32
tmp_n_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x368"

addr 0x368 @asm  "orrne r3, r3, #4"
label pc_0x368
PC:u32 = 0x368:u32
TmpV_23:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_23:bool , "L_45" , "pc_0x36C"
label L_45
tmp_r3:u32 = R3:u32 | low:u32(0x4:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x36C"

addr 0x36C @asm  "biceq r3, r3, #4"
label pc_0x36C
PC:u32 = 0x36C:u32
TmpV_24:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_24:bool , "L_47" , "pc_0x370"
label L_47
tmp_r3:u32 = (R3:u32 & low:u32(0xFFFFFFFB:u64))
R3:u32 = tmp_r3:u32
jmp  "pc_0x370"

addr 0x370 @asm  "mcr p15, #0, r3, c1, c0"
label pc_0x370

jmp "lift_error"

addr 0x374 @asm  "mov pc, lr"
label pc_0x374
PC:u32 = 0x374:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x378 @asm  "cmp r1, #0"
label pc_0x378
PC:u32 = 0x378:u32
tmp_n_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R1:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x37C"

addr 0x37C @asm  "beq +#32"
label pc_0x37C
PC:u32 = 0x37C:u32
TmpV_25:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_25:bool , "pc_0x39C" , "pc_0x380"

addr 0x380 @asm  "cmp r2, #0"
label pc_0x380
PC:u32 = 0x380:u32
tmp_n_flag:bool = low:bool(low:bool((R2:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R2:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R2:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R2:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R2:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R2:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R2:u32) >> 0x1f:u32 ) & ~(low:bool((R2:u32) >> 0x1f:u32 ) == ((((extend:u64(R2:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x384"

addr 0x384 @asm  "beq +#16"
label pc_0x384
PC:u32 = 0x384:u32
TmpV_26:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_26:bool , "pc_0x394" , "pc_0x388"


addr 0x388 @asm  "mrc p15, #0, pc, c7, c14, #3"
label pc_0x388

jmp "lift_error"

addr 0x38C @asm  "bne -#4"
label pc_0x38C
PC:u32 = 0x38C:u32
TmpV_27:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_27:bool , "pc_0x388" , "pc_0x390"

addr 0x390 @asm  "b +#12"
label pc_0x390
PC:u32 = 0x390:u32
jmp  "pc_0x39C"

addr 0x394 @asm  "mov r3, #1"
label pc_0x394
PC:u32 = 0x394:u32
tmp_r3:u32 = low:u32(0x1:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x398"

addr 0x398 @asm  "mcr p15, #0, r3, c7, c6"
label pc_0x398

jmp "lift_error"

addr 0x39C @asm  "cmp r0, #0"
label pc_0x39C
PC:u32 = 0x39C:u32
tmp_n_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x3A0"

addr 0x3A0 @asm  "moveq pc, lr"
label pc_0x3A0
PC:u32 = 0x3A0:u32
jmp "lift_error"
cjmp TmpV_28:bool , ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32) , "pc_0x3A4"

addr 0x3A4 @asm  "mov r3, #1"
label pc_0x3A4
PC:u32 = 0x3A4:u32
tmp_r3:u32 = low:u32(0x1:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x3A8"

addr 0x3A8 @asm  "mcr p15, #0, r3, c7, c5"
label pc_0x3A8

jmp "lift_error"

addr 0x3AC @asm  "mov pc, lr"
label pc_0x3AC
PC:u32 = 0x3AC:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x3B0 @asm  "mvn r2, #0"
label pc_0x3B0
PC:u32 = 0x3B0:u32
tmp_r2:u32 = low:u32(0xFFFFFFFF:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x3B4"

addr 0x3B4 @asm  "mvn r3, #48896"
label pc_0x3B4
PC:u32 = 0x3B4:u32
tmp_r3:u32 = low:u32(0xFFFF40FF:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x3B8"

addr 0x3B8 @asm  "str r2, [r3, #-251]"
label pc_0x3B8
PC:u32 = 0x3B8:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF05:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x3BC"

addr 0x3BC @asm  "mov pc, lr"
label pc_0x3BC
PC:u32 = 0x3BC:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x3C0 @asm  "push {r4, lr}"
label pc_0x3C0
PC:u32 = 0x3C0:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF8:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R4:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x3C4"

addr 0x3C4 @asm  "bl -#20"
label pc_0x3C4
PC:u32 = 0x3C4:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x3B0"

addr 0x3C8 @asm  "bl +#224"
label pc_0x3C8
PC:u32 = 0x3C8:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x4A8"

addr 0x3CC @asm  "bl +#496"
label pc_0x3CC
PC:u32 = 0x3CC:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x5BC"

addr 0x3D0 @asm  "pop {r4, lr}"
label pc_0x3D0
PC:u32 = 0x3D0:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x8:u64))
tmp_lr_svc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R4:u32 = tmp_r4:u32
SP_SVC:u32 = tmp_sp_svc:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x3D4"

addr 0x3D4 @asm  "b +#620"
label pc_0x3D4
PC:u32 = 0x3D4:u32
jmp  "pc_0x640"


addr 0x3D8 @asm  "push {r4, lr}"
label pc_0x3D8
PC:u32 = 0x3D8:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF8:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R4:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x3DC"

addr 0x3DC @asm  "mov r12, r1"
label pc_0x3DC
PC:u32 = 0x3DC:u32
tmp_r12:u32 = R1:u32
R12:u32 = tmp_r12:u32
jmp  "pc_0x3E0"

addr 0x3E0 @asm  "mov r4, r0"
label pc_0x3E0
PC:u32 = 0x3E0:u32
tmp_r4:u32 = R0:u32
R4:u32 = tmp_r4:u32
jmp  "pc_0x3E4"

addr 0x3E4 @asm  "ldr r0, [pc, #16]"
label pc_0x3E4
PC:u32 = 0x3E4:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x18:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x3E8"

addr 0x3E8 @asm  "mov r3, r2"
label pc_0x3E8
PC:u32 = 0x3E8:u32
tmp_r3:u32 = R2:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x3EC"

addr 0x3EC @asm  "mov r1, r4"
label pc_0x3EC
PC:u32 = 0x3EC:u32
tmp_r1:u32 = R4:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x3F0"

addr 0x3F0 @asm  "mov r2, r12"
label pc_0x3F0
PC:u32 = 0x3F0:u32
tmp_r2:u32 = R12:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x3F4"

addr 0x3F4 @asm  "pop {r4, lr}"
label pc_0x3F4
PC:u32 = 0x3F4:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x8:u64))
tmp_lr_svc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R4:u32 = tmp_r4:u32
SP_SVC:u32 = tmp_sp_svc:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x3F8"

addr 0x3F8 @asm  "b +#2660"
label pc_0x3F8
PC:u32 = 0x3F8:u32


addr 0x3FC @asm  "andeq r1, r0, r0, asr #1"
label pc_0x3FC
PC:u32 = 0x3FC:u32
TmpV_29:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_29:bool , "L_57" , "pc_0x400"
label L_57
tmp_r1:u32 = (R0:u32 & (R0:u32 $>> low:u32(0x1:u64)))
R1:u32 = tmp_r1:u32
jmp  "pc_0x400"


addr 0x400 @asm  "mov r0, #32"
label pc_0x400
PC:u32 = 0x400:u32
tmp_r0:u32 = low:u32(0x20:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x404"

addr 0x404 @asm  "mov pc, lr"
label pc_0x404
PC:u32 = 0x404:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x408 @asm  "cmp r0, #31"
label pc_0x408
PC:u32 = 0x408:u32
tmp_n_flag:bool = low:bool(low:bool(((R0:u32 + low:u32(0xFFFFFFE1:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R0:u32 + low:u32(0xFFFFFFE1:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x40C"

addr 0x40C @asm  "movhi pc, lr"
label pc_0x40C
PC:u32 = 0x40C:u32
jmp "pc_0x410"

PC:u32 = 0x40C:u32
jmp "lift_error"
cjmp TmpV_30:bool , ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32) , "pc_0x410"

addr 0x410 @asm  "mov r2, #1"
label pc_0x410
PC:u32 = 0x410:u32
tmp_r2:u32 = low:u32(0x1:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x414"

addr 0x414 @asm  "mov r0, r2, lsl r0"
label pc_0x414
PC:u32 = 0x414:u32
tmp_r0:u32 = (R2:u32 << low:u32(extend:u64(R0:u32)))
R0:u32 = tmp_r0:u32
jmp  "pc_0x418"

addr 0x418 @asm  "mvn r3, #3840"
label pc_0x418
PC:u32 = 0x418:u32
tmp_r3:u32 = low:u32(0xFFFFF0FF:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x41C"

addr 0x41C @asm  "cmp r1, #0"
label pc_0x41C
PC:u32 = 0x41C:u32
tmp_n_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R1:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x420"

addr 0x420 @asm  "strne r0, [r3, #33]"
label pc_0x420
PC:u32 = 0x420:u32
jmp "pc_0x424"

PC:u32 = 0x420:u32
jmp "lift_error"
cjmp TmpV_31:bool , "L_61" , "pc_0x424"
label L_61
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x21:u64)) ,e_little]:u32 =R0:u32
jmp  "pc_0x424"

addr 0x424 @asm  "streq r0, [r3, #37]"
label pc_0x424
PC:u32 = 0x424:u32
jmp "pc_0x428"

PC:u32 = 0x424:u32
jmp "lift_error"
cjmp TmpV_32:bool , "L_63" , "pc_0x428"
label L_63
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x25:u64)) ,e_little]:u32 =R0:u32
jmp  "pc_0x428"

addr 0x428 @asm  "mov r2, #0"
label pc_0x428
PC:u32 = 0x428:u32
tmp_r2:u32 = low:u32(0x0:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x42C"

addr 0x42C @asm  "mvn r3, #3840"
label pc_0x42C
PC:u32 = 0x42C:u32
tmp_r3:u32 = low:u32(0xFFFFF0FF:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x430"

addr 0x430 @asm  "str r2, [r3, #33]"
label pc_0x430
PC:u32 = 0x430:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x21:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x434"

addr 0x434 @asm  "str r2, [r3, #37]"
label pc_0x434
PC:u32 = 0x434:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x25:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x438"

addr 0x438 @asm  "mov pc, lr"
label pc_0x438
PC:u32 = 0x438:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x43C @asm  "cmp r0, #31"
label pc_0x43C
PC:u32 = 0x43C:u32
tmp_n_flag:bool = low:bool(low:bool(((R0:u32 + low:u32(0xFFFFFFE1:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R0:u32 + low:u32(0xFFFFFFE1:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x440"

addr 0x440 @asm  "movhi pc, lr"
label pc_0x440
PC:u32 = 0x440:u32
jmp "pc_0x444"

PC:u32 = 0x440:u32
jmp "lift_error"
cjmp TmpV_33:bool , ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32) , "pc_0x444"

addr 0x444 @asm  "ldr r3, [pc, #16]"
label pc_0x444
PC:u32 = 0x444:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x18:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x448"

addr 0x448 @asm  "cmp r1, #0"
label pc_0x448
PC:u32 = 0x448:u32
tmp_n_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R1:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x44C"

addr 0x44C @asm  "moveq r1, r3"
label pc_0x44C
PC:u32 = 0x44C:u32
TmpV_34:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_34:bool , "L_67" , "pc_0x450"
label L_67
tmp_r1:u32 = R3:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x450"

addr 0x450 @asm  "mov r0, r0, lsl #2"
label pc_0x450
PC:u32 = 0x450:u32
tmp_r0:u32 = (R0:u32 << low:u32(0x2:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0x454"

addr 0x454 @asm  "str r1, [r0, #-3968]"
label pc_0x454
PC:u32 = 0x454:u32
mem:?u32 = mem:?u32 with [(R0:u32 + low:u32(0xFFFFF080:u64)) ,e_little]:u32 =R1:u32
jmp  "pc_0x458"

addr 0x458 @asm  "mov pc, lr"
label pc_0x458
PC:u32 = 0x458:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x45C @asm  "ldrdeq r0, r1, [r0], -r8"
label pc_0x45C

jmp "lift_error"


addr 0x460 @asm  "cmp r0, #31"
label pc_0x460
PC:u32 = 0x460:u32
tmp_n_flag:bool = low:bool(low:bool(((R0:u32 + low:u32(0xFFFFFFE1:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R0:u32 + low:u32(0xFFFFFFE1:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x464"

addr 0x464 @asm  "movls r3, #1"
label pc_0x464
PC:u32 = 0x464:u32
jmp "lift_error"
cjmp TmpV_35:bool , "L_69" , "pc_0x468"
label L_69
tmp_r3:u32 = low:u32(0x1:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x468"

addr 0x468 @asm  "movls r0, r3, lsl r0"
label pc_0x468
PC:u32 = 0x468:u32
jmp "lift_error"
cjmp TmpV_36:bool , "L_71" , "pc_0x46C"
label L_71
tmp_r0:u32 = (R3:u32 << low:u32(extend:u64(R0:u32)))
R0:u32 = tmp_r0:u32
jmp  "pc_0x46C"

addr 0x46C @asm  "mvnls r3, #3840"
label pc_0x46C
PC:u32 = 0x46C:u32
jmp "lift_error"
cjmp TmpV_37:bool , "L_73" , "pc_0x470"
label L_73
tmp_r3:u32 = low:u32(0xFFFFF0FF:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x470"

addr 0x470 @asm  "strls r0, [r3, #49]"
label pc_0x470
PC:u32 = 0x470:u32
jmp "lift_error"
cjmp TmpV_38:bool , "L_75" , "pc_0x474"
label L_75
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x31:u64)) ,e_little]:u32 =R0:u32
jmp  "pc_0x474"

addr 0x474 @asm  "mov pc, lr"
label pc_0x474
PC:u32 = 0x474:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x478 @asm  "cmp r0, #31"
label pc_0x478
PC:u32 = 0x478:u32
tmp_n_flag:bool = low:bool(low:bool(((R0:u32 + low:u32(0xFFFFFFE1:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R0:u32 + low:u32(0xFFFFFFE1:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFE0:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x47C"

addr 0x47C @asm  "movhi pc, lr"
label pc_0x47C
PC:u32 = 0x47C:u32
jmp "pc_0x480"

PC:u32 = 0x47C:u32
jmp "lift_error"
cjmp TmpV_39:bool , ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32) , "pc_0x480"

addr 0x480 @asm  "and r1, r1, #7"
label pc_0x480
PC:u32 = 0x480:u32
tmp_r1:u32 = (R1:u32 & low:u32(0x7:u64))
R1:u32 = tmp_r1:u32
jmp  "pc_0x484"

addr 0x484 @asm  "cmp r2, #0"
label pc_0x484
PC:u32 = 0x484:u32
tmp_n_flag:bool = low:bool(low:bool((R2:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R2:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R2:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R2:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R2:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R2:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R2:u32) >> 0x1f:u32 ) & ~(low:bool((R2:u32) >> 0x1f:u32 ) == ((((extend:u64(R2:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x488"

addr 0x488 @asm  "orrne r1, r1, #64"
label pc_0x488
PC:u32 = 0x488:u32
TmpV_40:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_40:bool , "L_79" , "pc_0x48C"
label L_79
tmp_r1:u32 = R1:u32 | low:u32(0x40:u64)
R1:u32 = tmp_r1:u32
jmp  "pc_0x48C"

addr 0x48C @asm  "mov r0, r0, lsl #2"
label pc_0x48C
PC:u32 = 0x48C:u32
tmp_r0:u32 = (R0:u32 << low:u32(0x2:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0x490"

addr 0x490 @asm  "cmp r3, #0"
label pc_0x490
PC:u32 = 0x490:u32
tmp_n_flag:bool = low:bool(low:bool((R3:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R3:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R3:u32) >> 0x1f:u32 ) & ~(low:bool((R3:u32) >> 0x1f:u32 ) == ((((extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x494"

addr 0x494 @asm  "orreq r1, r1, #32"
label pc_0x494
PC:u32 = 0x494:u32
TmpV_41:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_41:bool , "L_81" , "pc_0x498"
label L_81
tmp_r1:u32 = R1:u32 | low:u32(0x20:u64)
R1:u32 = tmp_r1:u32
jmp  "pc_0x498"

addr 0x498 @asm  "sub r0, r0, #3840"
label pc_0x498
PC:u32 = 0x498:u32
tmp_r0:u32 = (R0:u32 + low:u32(0xFFFFF100:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0x49C"

addr 0x49C @asm  "str r1, [r0, #-256]"
label pc_0x49C
PC:u32 = 0x49C:u32
mem:?u32 = mem:?u32 with [(R0:u32 + low:u32(0xFFFFFF00:u64)) ,e_little]:u32 =R1:u32
jmp  "pc_0x4A0"

addr 0x4A0 @asm  "mov pc, lr"
label pc_0x4A0
PC:u32 = 0x4A0:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x4A4 @asm  "mov pc, lr"
label pc_0x4A4
PC:u32 = 0x4A4:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x4A8 @asm  "mvn r3, #3840"
label pc_0x4A8
PC:u32 = 0x4A8:u32
tmp_r3:u32 = low:u32(0xFFFFF0FF:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x4AC"

addr 0x4AC @asm  "mvn r2, #0"
label pc_0x4AC
PC:u32 = 0x4AC:u32
tmp_r2:u32 = low:u32(0xFFFFFFFF:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x4B0"

addr 0x4B0 @asm  "push {r4, lr}"
label pc_0x4B0
PC:u32 = 0x4B0:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF8:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R4:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x4B4"

addr 0x4B4 @asm  "str r2, [r3, #37]"
label pc_0x4B4
PC:u32 = 0x4B4:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x25:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x4B8"

addr 0x4B8 @asm  "str r2, [r3, #41]"
label pc_0x4B8
PC:u32 = 0x4B8:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x29:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x4BC"

addr 0x4BC @asm  "mov r4, #0"
label pc_0x4BC
PC:u32 = 0x4BC:u32
tmp_r4:u32 = low:u32(0x0:u64)
R4:u32 = tmp_r4:u32
jmp  "pc_0x4C0"

addr 0x4C0 @asm  "mov r0, r4"
label pc_0x4C0
PC:u32 = 0x4C0:u32
tmp_r0:u32 = R4:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x4C4"

addr 0x4C4 @asm  "mov r1, #0"
label pc_0x4C4
PC:u32 = 0x4C4:u32
tmp_r1:u32 = low:u32(0x0:u64)
R1:u32 = tmp_r1:u32
jmp  "pc_0x4C8"

addr 0x4C8 @asm  "bl -#192"
label pc_0x4C8
PC:u32 = 0x4C8:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x408"

addr 0x4CC @asm  "mov r0, r4"
label pc_0x4CC
PC:u32 = 0x4CC:u32
tmp_r0:u32 = R4:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x4D0"

addr 0x4D0 @asm  "ldr r1, [pc, #16]"
label pc_0x4D0
PC:u32 = 0x4D0:u32
tmp_r1:u32 = mem:?u32[(PC:u32 + low:u32(0x18:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x4D4"

addr 0x4D4 @asm  "add r4, r4, #1"
label pc_0x4D4
PC:u32 = 0x4D4:u32
tmp_r4:u32 = (R4:u32 + low:u32(0x1:u64))
R4:u32 = tmp_r4:u32
jmp  "pc_0x4D8"

addr 0x4D8 @asm  "bl -#156"
label pc_0x4D8
PC:u32 = 0x4D8:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x43C"

addr 0x4DC @asm  "cmp r4, #32"
label pc_0x4DC
PC:u32 = 0x4DC:u32
tmp_n_flag:bool = low:bool(low:bool(((R4:u32 + low:u32(0xFFFFFFE0:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R4:u32) + 0xFFFFFFDF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R4:u32) + 0xFFFFFFDF:u64 + 0x1:u64) else ((extend:u64(R4:u32) + 0xFFFFFFDF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R4:u32) + 0xFFFFFFDF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R4:u32 + low:u32(0xFFFFFFE0:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R4:u32) >> 0x1f:u32 ) & ~(low:bool((R4:u32) >> 0x1f:u32 ) == ((((extend:u64(R4:u32) + 0xFFFFFFDF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x4E0"

addr 0x4E0 @asm  "bne -#32"
label pc_0x4E0
PC:u32 = 0x4E0:u32
TmpV_42:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_42:bool , "pc_0x4C0" , "pc_0x4E4"

addr 0x4E4 @asm  "pop {r4, pc}"
label pc_0x4E4
PC:u32 = 0x4E4:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x8:u64))
tmp_r4:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
R4:u32 = tmp_r4:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp "lift_error"

addr 0x4E8 @asm  "ldrdeq r0, r1, [r0], -r8"
label pc_0x4E8

jmp "lift_error"


addr 0x4EC @asm  "push {r3, lr}"
label pc_0x4EC
PC:u32 = 0x4EC:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF8:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x4F0"

addr 0x4F0 @asm  "ldr r3, [pc, #28]"
label pc_0x4F0
PC:u32 = 0x4F0:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x24:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x4F4"

addr 0x4F4 @asm  "ldr r3, [r3, #-159]"
label pc_0x4F4
PC:u32 = 0x4F4:u32
tmp_r3:u32 = mem:?u32[(R3:u32 + low:u32(0xFFFFFF61:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x4F8"

addr 0x4F8 @asm  "ldr r3, [pc, #24]"
label pc_0x4F8
PC:u32 = 0x4F8:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x20:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x4FC"

addr 0x4FC @asm  "ldr r3, [r3]"
label pc_0x4FC
PC:u32 = 0x4FC:u32
tmp_r3:u32 = mem:?u32[R3:u32,e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x500"

addr 0x500 @asm  "cmp r3, #0"
label pc_0x500
PC:u32 = 0x500:u32
tmp_n_flag:bool = low:bool(low:bool((R3:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R3:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R3:u32) >> 0x1f:u32 ) & ~(low:bool((R3:u32) >> 0x1f:u32 ) == ((((extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x504"

addr 0x504 @asm  "popeq {r3, pc}"
label pc_0x504
PC:u32 = 0x504:u32
jmp "lift_error"
cjmp TmpV_43:bool , "L_85" , "pc_0x508"
label L_85
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x8:u64))
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x508"

addr 0x508 @asm  "mov lr, pc"
label pc_0x508
PC:u32 = 0x508:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x8:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x50C"

addr 0x50C @asm  "mov pc, r3"
label pc_0x50C
PC:u32 = 0x50C:u32
jmp  ( if (R3:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*R3:u32)$/low:u32(0x2:u64)) else R3:u32)

addr 0x510 @asm  "pop {r3, pc}"
label pc_0x510
PC:u32 = 0x510:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x8:u64))
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp "lift_error"

addr 0x514 @asm  "WORD 0xF6000010"
label pc_0x514

jmp "lift_error"

addr 0x518 @asm  "andeq r2, r0, r0, lsl r0"
label pc_0x518
PC:u32 = 0x518:u32
TmpV_44:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_44:bool , "L_87" , "pc_0x51C"
label L_87
tmp_r2:u32 = (R0:u32 & (R0:u32 << low:u32(extend:u64(R0:u32))))
R2:u32 = tmp_r2:u32
jmp  "pc_0x51C"


addr 0x51C @asm  "push {r4, lr}"
label pc_0x51C
PC:u32 = 0x51C:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF8:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R4:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x520"

addr 0x520 @asm  "ldr r4, [pc, #104]"
label pc_0x520
PC:u32 = 0x520:u32
tmp_r4:u32 = mem:?u32[(PC:u32 + low:u32(0x70:u64)),e_little]:u32
R4:u32 = tmp_r4:u32
jmp  "pc_0x524"

addr 0x524 @asm  "mov r3, #2"
label pc_0x524
PC:u32 = 0x524:u32
tmp_r3:u32 = low:u32(0x2:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x528"

addr 0x528 @asm  "str r3, [r4, #-191]"
label pc_0x528
PC:u32 = 0x528:u32
mem:?u32 = mem:?u32 with [(R4:u32 + low:u32(0xFFFFFF41:u64)) ,e_little]:u32 =R3:u32
jmp  "pc_0x52C"

addr 0x52C @asm  "mvn r3, #0"
label pc_0x52C
PC:u32 = 0x52C:u32
tmp_r3:u32 = low:u32(0xFFFFFFFF:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x530"

addr 0x530 @asm  "str r3, [r4, #-151]"
label pc_0x530
PC:u32 = 0x530:u32
mem:?u32 = mem:?u32 with [(R4:u32 + low:u32(0xFFFFFF69:u64)) ,e_little]:u32 =R3:u32
jmp  "pc_0x534"

addr 0x534 @asm  "ldr r3, [r4, #-159]"
label pc_0x534
PC:u32 = 0x534:u32
tmp_r3:u32 = mem:?u32[(R4:u32 + low:u32(0xFFFFFF61:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x538"

addr 0x538 @asm  "ldr r3, [pc, #84]"
label pc_0x538
PC:u32 = 0x538:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x5C:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x53C"

addr 0x53C @asm  "str r3, [r4, #-187]"
label pc_0x53C
PC:u32 = 0x53C:u32
mem:?u32 = mem:?u32 with [(R4:u32 + low:u32(0xFFFFFF45:u64)) ,e_little]:u32 =R3:u32
jmp  "pc_0x540"

addr 0x540 @asm  "ldr r3, [pc, #80]"
label pc_0x540
PC:u32 = 0x540:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x58:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x544"

addr 0x544 @asm  "ldr r1, [pc, #80]"
label pc_0x544
PC:u32 = 0x544:u32
tmp_r1:u32 = mem:?u32[(PC:u32 + low:u32(0x58:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x548"

addr 0x548 @asm  "str r0, [r3]"
label pc_0x548
PC:u32 = 0x548:u32
mem:?u32 = mem:?u32 with [R3:u32 ,e_little]:u32 =R0:u32
jmp  "pc_0x54C"

addr 0x54C @asm  "mov r0, #5"
label pc_0x54C
PC:u32 = 0x54C:u32
tmp_r0:u32 = low:u32(0x5:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x550"

addr 0x550 @asm  "bl -#276"
label pc_0x550
PC:u32 = 0x550:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x43C"

addr 0x554 @asm  "mov r2, #1"
label pc_0x554
PC:u32 = 0x554:u32
tmp_r2:u32 = low:u32(0x1:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x558"

addr 0x558 @asm  "mov r3, r2"
label pc_0x558
PC:u32 = 0x558:u32
tmp_r3:u32 = R2:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x55C"

addr 0x55C @asm  "mov r0, #5"
label pc_0x55C
PC:u32 = 0x55C:u32
tmp_r0:u32 = low:u32(0x5:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x560"

addr 0x560 @asm  "mov r1, #6"
label pc_0x560
PC:u32 = 0x560:u32
tmp_r1:u32 = low:u32(0x6:u64)
R1:u32 = tmp_r1:u32
jmp  "pc_0x564"

addr 0x564 @asm  "bl -#236"
label pc_0x564
PC:u32 = 0x564:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x478"

addr 0x568 @asm  "mov r3, #16"
label pc_0x568
PC:u32 = 0x568:u32
tmp_r3:u32 = low:u32(0x10:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x56C"

addr 0x56C @asm  "str r3, [r4, #-155]"
label pc_0x56C
PC:u32 = 0x56C:u32
mem:?u32 = mem:?u32 with [(R4:u32 + low:u32(0xFFFFFF65:u64)) ,e_little]:u32 =R3:u32
jmp  "pc_0x570"

addr 0x570 @asm  "mov r0, #5"
label pc_0x570
PC:u32 = 0x570:u32
tmp_r0:u32 = low:u32(0x5:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x574"

addr 0x574 @asm  "mov r1, #1"
label pc_0x574
PC:u32 = 0x574:u32
tmp_r1:u32 = low:u32(0x1:u64)
R1:u32 = tmp_r1:u32
jmp  "pc_0x578"

addr 0x578 @asm  "bl -#368"
label pc_0x578
PC:u32 = 0x578:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x408"

addr 0x57C @asm  "mov r3, #1"
label pc_0x57C
PC:u32 = 0x57C:u32
tmp_r3:u32 = low:u32(0x1:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x580"

addr 0x580 @asm  "str r3, [r4, #-191]"
label pc_0x580
PC:u32 = 0x580:u32
mem:?u32 = mem:?u32 with [(R4:u32 + low:u32(0xFFFFFF41:u64)) ,e_little]:u32 =R3:u32
jmp  "pc_0x584"

addr 0x584 @asm  "mov r3, #312"
label pc_0x584
PC:u32 = 0x584:u32
tmp_r3:u32 = low:u32(0x138:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x588"

addr 0x588 @asm  "str r3, [r4, #-163]"
label pc_0x588
PC:u32 = 0x588:u32
mem:?u32 = mem:?u32 with [(R4:u32 + low:u32(0xFFFFFF5D:u64)) ,e_little]:u32 =R3:u32
jmp  "pc_0x58C"

addr 0x58C @asm  "pop {r4, pc}"
label pc_0x58C
PC:u32 = 0x58C:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x8:u64))
tmp_r4:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
R4:u32 = tmp_r4:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp "lift_error"

addr 0x590 @asm  "WORD 0xF6000010"
label pc_0x590

jmp "lift_error"

addr 0x594 @asm  "andeq r4, r0, r4"
label pc_0x594
PC:u32 = 0x594:u32
TmpV_45:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_45:bool , "L_89" , "pc_0x598"
label L_89
tmp_r4:u32 = (R0:u32 & R4:u32)
R4:u32 = tmp_r4:u32
jmp  "pc_0x598"

addr 0x598 @asm  "andeq r2, r0, r0, lsl r0"
label pc_0x598
PC:u32 = 0x598:u32
TmpV_46:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_46:bool , "L_91" , "pc_0x59C"
label L_91
tmp_r2:u32 = (R0:u32 & (R0:u32 << low:u32(extend:u64(R0:u32))))
R2:u32 = tmp_r2:u32
jmp  "pc_0x59C"

addr 0x59C @asm  "andeq r0, r0, r12, ror #9"
label pc_0x59C
PC:u32 = 0x59C:u32
TmpV_47:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_47:bool , "L_93" , "pc_0x5A0"
label L_93
jmp "lift_error"
R0:u32 = tmp_r0:u32
jmp  "pc_0x5A0"


addr 0x5A0 @asm  "ldr r3, [pc, #16]"
label pc_0x5A0
PC:u32 = 0x5A0:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x18:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x5A4"

addr 0x5A4 @asm  "mov r2, #2"
label pc_0x5A4
PC:u32 = 0x5A4:u32
tmp_r2:u32 = low:u32(0x2:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x5A8"

addr 0x5A8 @asm  "str r2, [r3, #-191]"
label pc_0x5A8
PC:u32 = 0x5A8:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF41:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x5AC"

addr 0x5AC @asm  "mvn r2, #0"
label pc_0x5AC
PC:u32 = 0x5AC:u32
tmp_r2:u32 = low:u32(0xFFFFFFFF:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x5B0"

addr 0x5B0 @asm  "str r2, [r3, #-151]"
label pc_0x5B0
PC:u32 = 0x5B0:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF69:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x5B4"

addr 0x5B4 @asm  "mov pc, lr"
label pc_0x5B4
PC:u32 = 0x5B4:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x5B8 @asm  "WORD 0xF6000010"
label pc_0x5B8

jmp "lift_error"


addr 0x5BC @asm  "ldr r3, [pc, #32]"
label pc_0x5BC
PC:u32 = 0x5BC:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x28:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x5C0"

addr 0x5C0 @asm  "mov r2, #3"
label pc_0x5C0
PC:u32 = 0x5C0:u32
tmp_r2:u32 = low:u32(0x3:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x5C4"

addr 0x5C4 @asm  "str r2, [r3, #-255]"
label pc_0x5C4
PC:u32 = 0x5C4:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF01:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x5C8"

addr 0x5C8 @asm  "str r2, [r3, #-191]"
label pc_0x5C8
PC:u32 = 0x5C8:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF41:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x5CC"

addr 0x5CC @asm  "str r2, [r3, #-127]"
label pc_0x5CC
PC:u32 = 0x5CC:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF81:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x5D0"

addr 0x5D0 @asm  "mvn r2, #0"
label pc_0x5D0
PC:u32 = 0x5D0:u32
tmp_r2:u32 = low:u32(0xFFFFFFFF:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x5D4"

addr 0x5D4 @asm  "str r2, [r3, #-215]"
label pc_0x5D4
PC:u32 = 0x5D4:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF29:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x5D8"

addr 0x5D8 @asm  "str r2, [r3, #-151]"
label pc_0x5D8
PC:u32 = 0x5D8:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF69:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x5DC"

addr 0x5DC @asm  "str r2, [r3, #-87]"
label pc_0x5DC
PC:u32 = 0x5DC:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFFA9:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x5E0"

addr 0x5E0 @asm  "mov pc, lr"
label pc_0x5E0
PC:u32 = 0x5E0:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x5E4 @asm  "WORD 0xF6000010"
label pc_0x5E4

jmp "lift_error"


addr 0x5E8 @asm  "ldr r3, [pc, #32]"
label pc_0x5E8
PC:u32 = 0x5E8:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x28:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x5EC"

addr 0x5EC @asm  "ldr r2, [r3, #-195]"
label pc_0x5EC
PC:u32 = 0x5EC:u32
tmp_r2:u32 = mem:?u32[(R3:u32 + low:u32(0xFFFFFF3D:u64)),e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x5F0"

addr 0x5F0 @asm  "cmp r2, #0"
label pc_0x5F0
PC:u32 = 0x5F0:u32
tmp_n_flag:bool = low:bool(low:bool((R2:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R2:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R2:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R2:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R2:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R2:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R2:u32) >> 0x1f:u32 ) & ~(low:bool((R2:u32) >> 0x1f:u32 ) == ((((extend:u64(R2:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x5F4"

addr 0x5F4 @asm  "bne -#12"
label pc_0x5F4
PC:u32 = 0x5F4:u32
TmpV_48:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_48:bool , "pc_0x5E8" , "pc_0x5F8"

addr 0x5F8 @asm  "ldr r2, [pc, #20]"
label pc_0x5F8
PC:u32 = 0x5F8:u32
tmp_r2:u32 = mem:?u32[(PC:u32 + low:u32(0x1C:u64)),e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x5FC"

addr 0x5FC @asm  "strb r0, [r2]"
label pc_0x5FC
PC:u32 = 0x5FC:u32
mem:?u32 = mem:?u32 with [R2:u32 ,e_little]:u8 = (low:u8(R0:u32))jmp  "pc_0x600"

addr 0x600 @asm  "str r2, [r3, #-199]"
label pc_0x600
PC:u32 = 0x600:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF39:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x604"

addr 0x604 @asm  "mov r2, #1"
label pc_0x604
PC:u32 = 0x604:u32
tmp_r2:u32 = low:u32(0x1:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x608"

addr 0x608 @asm  "str r2, [r3, #-195]"
label pc_0x608
PC:u32 = 0x608:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF3D:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x60C"

addr 0x60C @asm  "mov pc, lr"
label pc_0x60C
PC:u32 = 0x60C:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x610 @asm  "WORD 0xF6000010"
label pc_0x610

jmp "lift_error"

addr 0x614 @asm  "andeq r2, r0, r4, lsl r0"
label pc_0x614
PC:u32 = 0x614:u32
TmpV_49:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_49:bool , "L_97" , "pc_0x618"
label L_97
tmp_r2:u32 = (R0:u32 & (R4:u32 << low:u32(extend:u64(R0:u32))))
R2:u32 = tmp_r2:u32
jmp  "pc_0x618"


addr 0x618 @asm  "mvn r0, #0"
label pc_0x618
PC:u32 = 0x618:u32
tmp_r0:u32 = low:u32(0xFFFFFFFF:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x61C"

addr 0x61C @asm  "mov pc, lr"
label pc_0x61C
PC:u32 = 0x61C:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x620 @asm  "ldr r3, [pc, #12]"
label pc_0x620
PC:u32 = 0x620:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x14:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x624"

addr 0x624 @asm  "ldr r0, [r3, #-195]"
label pc_0x624
PC:u32 = 0x624:u32
tmp_r0:u32 = mem:?u32[(R3:u32 + low:u32(0xFFFFFF3D:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x628"

addr 0x628 @asm  "rsbs r0, r0, #1"
label pc_0x628
PC:u32 = 0x628:u32
tmp_r0:u32 = (low:u32(0x1:u64) +  -R0:u32)
tmp_n_flag:bool = low:bool(low:bool(((low:u32(0x1:u64) +  -R0:u32)) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64( ~R0:u32) + 0x1:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64( ~R0:u32) + 0x1:u64 + 0x1:u64) else ((extend:u64( ~R0:u32) + 0x1:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64( ~R0:u32) + 0x1:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((low:u32(0x1:u64) == R0:u32))
tmp_v_flag:bool = low:bool(~low:bool(( ~R0:u32) >> 0x1f:u32 ) & ~(low:bool(( ~R0:u32) >> 0x1f:u32 ) == ((((extend:u64( ~R0:u32) + 0x1:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
R0:u32 = tmp_r0:u32
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x62C"

addr 0x62C @asm  "movcc r0, #0"
label pc_0x62C
PC:u32 = 0x62C:u32
TmpV_50:bool = low:bool( ~C_FLAG:bool)
cjmp TmpV_50:bool , "L_99" , "pc_0x630"
label L_99
tmp_r0:u32 = low:u32(0x0:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x630"

addr 0x630 @asm  "mov pc, lr"
label pc_0x630
PC:u32 = 0x630:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x634 @asm  "WORD 0xF6000010"
label pc_0x634

jmp "lift_error"


addr 0x638 @asm  "mov r0, #0"
label pc_0x638
PC:u32 = 0x638:u32
tmp_r0:u32 = low:u32(0x0:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x63C"

addr 0x63C @asm  "mov pc, lr"
label pc_0x63C
PC:u32 = 0x63C:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x640 @asm  "ldr r3, [pc, #68]"
label pc_0x640
PC:u32 = 0x640:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x4C:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x644"

addr 0x644 @asm  "mov r2, #172"
label pc_0x644
PC:u32 = 0x644:u32
tmp_r2:u32 = low:u32(0xAC:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x648"

addr 0x648 @asm  "str r2, [r3, #-255]"
label pc_0x648
PC:u32 = 0x648:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF01:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x64C"

addr 0x64C @asm  "mvn r2, #0"
label pc_0x64C
PC:u32 = 0x64C:u32
tmp_r2:u32 = low:u32(0xFFFFFFFF:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x650"

addr 0x650 @asm  "str r2, [r3, #-243]"
label pc_0x650
PC:u32 = 0x650:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF0D:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x654"

addr 0x654 @asm  "mov r2, #2512"
label pc_0x654
PC:u32 = 0x654:u32
tmp_r2:u32 = low:u32(0x9D0:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x658"

addr 0x658 @asm  "str r2, [r3, #-251]"
label pc_0x658
PC:u32 = 0x658:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF05:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x65C"

addr 0x65C @asm  "mov r2, #10"
label pc_0x65C
PC:u32 = 0x65C:u32
tmp_r2:u32 = low:u32(0xA:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x660"

addr 0x660 @asm  "str r2, [r3, #-223]"
label pc_0x660
PC:u32 = 0x660:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF21:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x664"

addr 0x664 @asm  "ldr r2, [pc, #36]"
label pc_0x664
PC:u32 = 0x664:u32
tmp_r2:u32 = mem:?u32[(PC:u32 + low:u32(0x2C:u64)),e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x668"

addr 0x668 @asm  "add r1, r2, #16"
label pc_0x668
PC:u32 = 0x668:u32
tmp_r1:u32 = (R2:u32 + low:u32(0x10:u64))
R1:u32 = tmp_r1:u32
jmp  "pc_0x66C"

addr 0x66C @asm  "str r1, [r3, #-207]"
label pc_0x66C
PC:u32 = 0x66C:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF31:u64)) ,e_little]:u32 =R1:u32
jmp  "pc_0x670"

addr 0x670 @asm  "str r2, [r3, #-199]"
label pc_0x670
PC:u32 = 0x670:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF39:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x674"

addr 0x674 @asm  "mov r2, #0"
label pc_0x674
PC:u32 = 0x674:u32
tmp_r2:u32 = low:u32(0x0:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x678"

addr 0x678 @asm  "str r2, [r3, #-195]"
label pc_0x678
PC:u32 = 0x678:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF3D:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x67C"

addr 0x67C @asm  "str r2, [r3, #-203]"
label pc_0x67C
PC:u32 = 0x67C:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF35:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x680"

addr 0x680 @asm  "add r2, r2, #80"
label pc_0x680
PC:u32 = 0x680:u32
tmp_r2:u32 = (R2:u32 + low:u32(0x50:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0x684"

addr 0x684 @asm  "str r2, [r3, #-255]"
label pc_0x684
PC:u32 = 0x684:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFF01:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x688"

addr 0x688 @asm  "mov pc, lr"
label pc_0x688
PC:u32 = 0x688:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x68C @asm  "WORD 0xF6000010"
label pc_0x68C

jmp "lift_error"

addr 0x690 @asm  "andeq r2, r0, r4, lsl r0"
label pc_0x690
PC:u32 = 0x690:u32
TmpV_51:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_51:bool , "L_101" , "pc_0x694"
label L_101
tmp_r2:u32 = (R0:u32 & (R4:u32 << low:u32(extend:u64(R0:u32))))
R2:u32 = tmp_r2:u32
jmp  "pc_0x694"


addr 0x694 @asm  "ldr r3, [pc, #68]"
label pc_0x694
PC:u32 = 0x694:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x4C:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x698"

addr 0x698 @asm  "ldr r3, [r3]"
label pc_0x698
PC:u32 = 0x698:u32
tmp_r3:u32 = mem:?u32[R3:u32,e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x69C"

addr 0x69C @asm  "ldr r2, [r3, #160]"
label pc_0x69C
PC:u32 = 0x69C:u32
tmp_r2:u32 = mem:?u32[(R3:u32 + low:u32(0xA0:u64)),e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x6A0"

addr 0x6A0 @asm  "ldr r1, [r2, #76]"
label pc_0x6A0
PC:u32 = 0x6A0:u32
tmp_r1:u32 = mem:?u32[(R2:u32 + low:u32(0x4C:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x6A4"

addr 0x6A4 @asm  "str r1, [r3, #80]"
label pc_0x6A4
PC:u32 = 0x6A4:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x50:u64)) ,e_little]:u32 =R1:u32
jmp  "pc_0x6A8"

addr 0x6A8 @asm  "ldr r1, [r2, #80]"
label pc_0x6A8
PC:u32 = 0x6A8:u32
tmp_r1:u32 = mem:?u32[(R2:u32 + low:u32(0x50:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x6AC"

addr 0x6AC @asm  "str r1, [r3, #152]"
label pc_0x6AC
PC:u32 = 0x6AC:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x98:u64)) ,e_little]:u32 =R1:u32
jmp  "pc_0x6B0"

addr 0x6B0 @asm  "mvn r1, #0"
label pc_0x6B0
PC:u32 = 0x6B0:u32
tmp_r1:u32 = low:u32(0xFFFFFFFF:u64)
R1:u32 = tmp_r1:u32
jmp  "pc_0x6B4"

addr 0x6B4 @asm  "str r1, [r3, #4]"
label pc_0x6B4
PC:u32 = 0x6B4:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x4:u64)) ,e_little]:u32 =R1:u32
jmp  "pc_0x6B8"

addr 0x6B8 @asm  "str r1, [r3, #8]"
label pc_0x6B8
PC:u32 = 0x6B8:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x8:u64)) ,e_little]:u32 =R1:u32
jmp  "pc_0x6BC"

addr 0x6BC @asm  "add r1, r1, #1"
label pc_0x6BC
PC:u32 = 0x6BC:u32
tmp_r1:u32 = (R1:u32 + low:u32(0x1:u64))
R1:u32 = tmp_r1:u32
jmp  "pc_0x6C0"

addr 0x6C0 @asm  "str r1, [r3, #156]"
label pc_0x6C0
PC:u32 = 0x6C0:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x9C:u64)) ,e_little]:u32 =R1:u32
jmp  "pc_0x6C4"

addr 0x6C4 @asm  "ldmia r2, {r1, r2}"
label pc_0x6C4
PC:u32 = 0x6C4:u32
tmp_r2:u32 = mem:?u32[(R2:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r1:u32 = mem:?u32[R2:u32,e_little]:u32
R1:u32 = tmp_r1:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x6C8"

addr 0x6C8 @asm  "mov r0, #1"
label pc_0x6C8
PC:u32 = 0x6C8:u32
tmp_r0:u32 = low:u32(0x1:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x6CC"

addr 0x6CC @asm  "str r2, [r3, #136]"
label pc_0x6CC
PC:u32 = 0x6CC:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x88:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x6D0"

addr 0x6D0 @asm  "mov r2, #208"
label pc_0x6D0
PC:u32 = 0x6D0:u32
tmp_r2:u32 = low:u32(0xD0:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x6D4"

addr 0x6D4 @asm  "str r1, [r3, #144]"
label pc_0x6D4
PC:u32 = 0x6D4:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x90:u64)) ,e_little]:u32 =R1:u32
jmp  "pc_0x6D8"

addr 0x6D8 @asm  "str r2, [r3, #148]"
label pc_0x6D8
PC:u32 = 0x6D8:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x94:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x6DC"

addr 0x6DC @asm  "b +#392"
label pc_0x6DC
PC:u32 = 0x6DC:u32
jmp  "pc_0x864"

addr 0x6E0 @asm  "andeq r8, r0, r0, lsr r1"
label pc_0x6E0
PC:u32 = 0x6E0:u32
TmpV_52:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_52:bool , "L_103" , "pc_0x6E4"
label L_103
tmp_r8:u32 = (R0:u32 & (R0:u32 >> low:u32(extend:u64(R1:u32))))
R8:u32 = tmp_r8:u32
jmp  "pc_0x6E4"


addr 0x6E4 @asm  "push {r4-r6, lr}"
label pc_0x6E4
PC:u32 = 0x6E4:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF0:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R6:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF4:u64)) ,e_little]:u32 =R5:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF0:u64)) ,e_little]:u32 =R4:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x6E8"

addr 0x6E8 @asm  "ldr r0, [pc, #60]"
label pc_0x6E8
PC:u32 = 0x6E8:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x44:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x6EC"

addr 0x6EC @asm  "mov r5, r2"
label pc_0x6EC
PC:u32 = 0x6EC:u32
tmp_r5:u32 = R2:u32
R5:u32 = tmp_r5:u32
jmp  "pc_0x6F0"

addr 0x6F0 @asm  "mov r4, r1"
label pc_0x6F0
PC:u32 = 0x6F0:u32
tmp_r4:u32 = R1:u32
R4:u32 = tmp_r4:u32
jmp  "pc_0x6F4"

addr 0x6F4 @asm  "mov r1, r2"
label pc_0x6F4
PC:u32 = 0x6F4:u32
tmp_r1:u32 = R2:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x6F8"

addr 0x6F8 @asm  "bl +#1892"
label pc_0x6F8
PC:u32 = 0x6F8:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32


addr 0x6FC @asm  "cmp r5, #0"
label pc_0x6FC
PC:u32 = 0x6FC:u32
tmp_n_flag:bool = low:bool(low:bool((R5:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R5:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R5:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R5:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R5:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R5:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R5:u32) >> 0x1f:u32 ) & ~(low:bool((R5:u32) >> 0x1f:u32 ) == ((((extend:u64(R5:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x700"

addr 0x700 @asm  "beq +#24"
label pc_0x700
PC:u32 = 0x700:u32
TmpV_53:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_53:bool , "pc_0x718" , "pc_0x704"

addr 0x704 @asm  "cmp r5, #1"
label pc_0x704
PC:u32 = 0x704:u32
tmp_n_flag:bool = low:bool(low:bool(((R5:u32 + low:u32(0xFFFFFFFF:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R5:u32) + 0xFFFFFFFE:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R5:u32) + 0xFFFFFFFE:u64 + 0x1:u64) else ((extend:u64(R5:u32) + 0xFFFFFFFE:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R5:u32) + 0xFFFFFFFE:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R5:u32 + low:u32(0xFFFFFFFF:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R5:u32) >> 0x1f:u32 ) & ~(low:bool((R5:u32) >> 0x1f:u32 ) == ((((extend:u64(R5:u32) + 0xFFFFFFFE:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x708"

addr 0x708 @asm  "bne +#24"
label pc_0x708
PC:u32 = 0x708:u32
TmpV_54:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_54:bool , "pc_0x720" , "pc_0x70C"

addr 0x70C @asm  "mov r0, r4"
label pc_0x70C
PC:u32 = 0x70C:u32
tmp_r0:u32 = R4:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x710"

addr 0x710 @asm  "pop {r4-r6, lr}"
label pc_0x710
PC:u32 = 0x710:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x10:u64))
tmp_lr_svc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r6:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r5:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R4:u32 = tmp_r4:u32
R5:u32 = tmp_r5:u32
R6:u32 = tmp_r6:u32
SP_SVC:u32 = tmp_sp_svc:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x714"

addr 0x714 @asm  "b +#404"
label pc_0x714
PC:u32 = 0x714:u32
jmp  "pc_0x8A8"

addr 0x718 @asm  "pop {r4-r6, lr}"
label pc_0x718
PC:u32 = 0x718:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x10:u64))
tmp_lr_svc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r6:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r5:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R4:u32 = tmp_r4:u32
R5:u32 = tmp_r5:u32
R6:u32 = tmp_r6:u32
SP_SVC:u32 = tmp_sp_svc:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x71C"

addr 0x71C @asm  "b +#484"
label pc_0x71C
PC:u32 = 0x71C:u32
jmp  "pc_0x900"

addr 0x720 @asm  "mov r0, r5"
label pc_0x720
PC:u32 = 0x720:u32
tmp_r0:u32 = R5:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x724"

addr 0x724 @asm  "pop {r4-r6, lr}"
label pc_0x724
PC:u32 = 0x724:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x10:u64))
tmp_lr_svc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r6:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r5:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R4:u32 = tmp_r4:u32
R5:u32 = tmp_r5:u32
R6:u32 = tmp_r6:u32
SP_SVC:u32 = tmp_sp_svc:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x728"

addr 0x728 @asm  "b +#416"
label pc_0x728
PC:u32 = 0x728:u32
jmp  "pc_0x8C8"

addr 0x72C @asm  "andeq r1, r0, r4, ror #1"
label pc_0x72C
PC:u32 = 0x72C:u32
TmpV_55:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_55:bool , "L_109" , "pc_0x730"
label L_109
jmp "lift_error"
R1:u32 = tmp_r1:u32
jmp  "pc_0x730"


addr 0x730 @asm  "push {r3, lr}"
label pc_0x730
PC:u32 = 0x730:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF8:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x734"

addr 0x734 @asm  "mov r3, r0"
label pc_0x734
PC:u32 = 0x734:u32
tmp_r3:u32 = R0:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x738"

addr 0x738 @asm  "mov r2, r1"
label pc_0x738
PC:u32 = 0x738:u32
tmp_r2:u32 = R1:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x73C"

addr 0x73C @asm  "ldr r0, [pc, #16]"
label pc_0x73C
PC:u32 = 0x73C:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x18:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x740"

addr 0x740 @asm  "mov r1, r3"
label pc_0x740
PC:u32 = 0x740:u32
tmp_r1:u32 = R3:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x744"

addr 0x744 @asm  "bl +#1816"
label pc_0x744
PC:u32 = 0x744:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32


addr 0x748 @asm  "bl -#180"
label pc_0x748
PC:u32 = 0x748:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x694"

addr 0x74C @asm  "mov r0, #0"
label pc_0x74C
PC:u32 = 0x74C:u32
tmp_r0:u32 = low:u32(0x0:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x750"

addr 0x750 @asm  "pop {r3, pc}"
label pc_0x750
PC:u32 = 0x750:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x8:u64))
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp "lift_error"

addr 0x754 @asm  "strdeq r1, r2, [r0], -pc"
label pc_0x754

jmp "lift_error"


addr 0x758 @asm  "push {r3, lr}"
label pc_0x758
PC:u32 = 0x758:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF8:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x75C"

addr 0x75C @asm  "mov r3, r0"
label pc_0x75C
PC:u32 = 0x75C:u32
tmp_r3:u32 = R0:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x760"

addr 0x760 @asm  "mov r2, r1"
label pc_0x760
PC:u32 = 0x760:u32
tmp_r2:u32 = R1:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x764"

addr 0x764 @asm  "ldr r0, [pc, #16]"
label pc_0x764
PC:u32 = 0x764:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x18:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x768"

addr 0x768 @asm  "mov r1, r3"
label pc_0x768
PC:u32 = 0x768:u32
tmp_r1:u32 = R3:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x76C"

addr 0x76C @asm  "bl +#1776"
label pc_0x76C
PC:u32 = 0x76C:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32


addr 0x770 @asm  "bl -#220"
label pc_0x770
PC:u32 = 0x770:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x694"

addr 0x774 @asm  "mov r0, #0"
label pc_0x774
PC:u32 = 0x774:u32
tmp_r0:u32 = low:u32(0x0:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x778"

addr 0x778 @asm  "pop {r3, pc}"
label pc_0x778
PC:u32 = 0x778:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x8:u64))
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp "lift_error"

addr 0x77C @asm  "andeq r1, r0, r2, lsr #2"
label pc_0x77C
PC:u32 = 0x77C:u32
TmpV_56:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_56:bool , "L_111" , "pc_0x780"
label L_111
tmp_r1:u32 = (R0:u32 & (R2:u32 >> low:u32(0x2:u64)))
R1:u32 = tmp_r1:u32
jmp  "pc_0x780"


addr 0x780 @asm  "push {r4-r6, lr}"
label pc_0x780
PC:u32 = 0x780:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF0:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R6:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF4:u64)) ,e_little]:u32 =R5:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF0:u64)) ,e_little]:u32 =R4:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x784"

addr 0x784 @asm  "ldr r4, [pc, #168]"
label pc_0x784
PC:u32 = 0x784:u32
tmp_r4:u32 = mem:?u32[(PC:u32 + low:u32(0xB0:u64)),e_little]:u32
R4:u32 = tmp_r4:u32
jmp  "pc_0x788"

addr 0x788 @asm  "ldr r0, [pc, #168]"
label pc_0x788
PC:u32 = 0x788:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0xB0:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x78C"

addr 0x78C @asm  "bl +#1744"
label pc_0x78C
PC:u32 = 0x78C:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32


addr 0x790 @asm  "ldr r2, [r4]"
label pc_0x790
PC:u32 = 0x790:u32
tmp_r2:u32 = mem:?u32[R4:u32,e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x794"

addr 0x794 @asm  "ldr r3, [r2, #164]"
label pc_0x794
PC:u32 = 0x794:u32
tmp_r3:u32 = mem:?u32[(R2:u32 + low:u32(0xA4:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x798"

addr 0x798 @asm  "ldr r1, [r3, #172]"
label pc_0x798
PC:u32 = 0x798:u32
tmp_r1:u32 = mem:?u32[(R3:u32 + low:u32(0xAC:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x79C"

addr 0x79C @asm  "cmp r1, #0"
label pc_0x79C
PC:u32 = 0x79C:u32
tmp_n_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R1:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x7A0"

addr 0x7A0 @asm  "mov r1, r4"
label pc_0x7A0
PC:u32 = 0x7A0:u32
tmp_r1:u32 = R4:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x7A4"

addr 0x7A4 @asm  "beq +#112"
label pc_0x7A4
PC:u32 = 0x7A4:u32
TmpV_57:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_57:bool , "pc_0x814" , "pc_0x7A8"

addr 0x7A8 @asm  "ldr r0, [r3, #4]"
label pc_0x7A8
PC:u32 = 0x7A8:u32
tmp_r0:u32 = mem:?u32[(R3:u32 + low:u32(0x4:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x7AC"

addr 0x7AC @asm  "cmp r0, #1"
label pc_0x7AC
PC:u32 = 0x7AC:u32
tmp_n_flag:bool = low:bool(low:bool(((R0:u32 + low:u32(0xFFFFFFFF:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R0:u32 + low:u32(0xFFFFFFFF:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x7B0"

addr 0x7B0 @asm  "bne +#100"
label pc_0x7B0
PC:u32 = 0x7B0:u32
TmpV_58:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_58:bool , "pc_0x814" , "pc_0x7B4"

addr 0x7B4 @asm  "mov r1, #0"
label pc_0x7B4
PC:u32 = 0x7B4:u32
tmp_r1:u32 = low:u32(0x0:u64)
R1:u32 = tmp_r1:u32
jmp  "pc_0x7B8"

addr 0x7B8 @asm  "str r1, [r3, #172]"
label pc_0x7B8
PC:u32 = 0x7B8:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xAC:u64)) ,e_little]:u32 =R1:u32
jmp  "pc_0x7BC"

addr 0x7BC @asm  "ldr r3, [r2, #4]"
label pc_0x7BC
PC:u32 = 0x7BC:u32
tmp_r3:u32 = mem:?u32[(R2:u32 + low:u32(0x4:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x7C0"

addr 0x7C0 @asm  "add r0, r0, #191"
label pc_0x7C0
PC:u32 = 0x7C0:u32
tmp_r0:u32 = (R0:u32 + low:u32(0xBF:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0x7C4"

addr 0x7C4 @asm  "str r3, [r2, #8]"
label pc_0x7C4
PC:u32 = 0x7C4:u32
mem:?u32 = mem:?u32 with [(R2:u32 + low:u32(0x8:u64)) ,e_little]:u32 =R3:u32
jmp  "pc_0x7C8"

addr 0x7C8 @asm  "bl +#1372"
label pc_0x7C8
PC:u32 = 0x7C8:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xD24"

addr 0x7CC @asm  "ldr r3, [r4]"
label pc_0x7CC
PC:u32 = 0x7CC:u32
tmp_r3:u32 = mem:?u32[R4:u32,e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x7D0"

addr 0x7D0 @asm  "ldr r3, [r3, #164]"
label pc_0x7D0
PC:u32 = 0x7D0:u32
tmp_r3:u32 = mem:?u32[(R3:u32 + low:u32(0xA4:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x7D4"

addr 0x7D4 @asm  "str r3, [r4]"
label pc_0x7D4
PC:u32 = 0x7D4:u32
mem:?u32 = mem:?u32 with [R4:u32 ,e_little]:u32 =R3:u32
jmp  "pc_0x7D8"

addr 0x7D8 @asm  "ldr r3, [r3, #160]"
label pc_0x7D8
PC:u32 = 0x7D8:u32
tmp_r3:u32 = mem:?u32[(R3:u32 + low:u32(0xA0:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x7DC"

addr 0x7DC @asm  "mov r5, r0"
label pc_0x7DC
PC:u32 = 0x7DC:u32
tmp_r5:u32 = R0:u32
R5:u32 = tmp_r5:u32
jmp  "pc_0x7E0"

addr 0x7E0 @asm  "ldr r0, [r3, #84]"
label pc_0x7E0
PC:u32 = 0x7E0:u32
tmp_r0:u32 = mem:?u32[(R3:u32 + low:u32(0x54:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x7E4"

addr 0x7E4 @asm  "bl +#128"
label pc_0x7E4
PC:u32 = 0x7E4:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x864"

addr 0x7E8 @asm  "ldr r2, [r4]"
label pc_0x7E8
PC:u32 = 0x7E8:u32
tmp_r2:u32 = mem:?u32[R4:u32,e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x7EC"

addr 0x7EC @asm  "ldr r1, [r2, #160]"
label pc_0x7EC
PC:u32 = 0x7EC:u32
tmp_r1:u32 = mem:?u32[(R2:u32 + low:u32(0xA0:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x7F0"

addr 0x7F0 @asm  "ldr r3, [r2, #156]"
label pc_0x7F0
PC:u32 = 0x7F0:u32
tmp_r3:u32 = mem:?u32[(R2:u32 + low:u32(0x9C:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x7F4"

addr 0x7F4 @asm  "ldr r2, [r2, #168]"
label pc_0x7F4
PC:u32 = 0x7F4:u32
tmp_r2:u32 = mem:?u32[(R2:u32 + low:u32(0xA8:u64)),e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x7F8"

addr 0x7F8 @asm  "ldr r0, [r1, #92]"
label pc_0x7F8
PC:u32 = 0x7F8:u32
tmp_r0:u32 = mem:?u32[(R1:u32 + low:u32(0x5C:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x7FC"

addr 0x7FC @asm  "str r2, [r3]"
label pc_0x7FC
PC:u32 = 0x7FC:u32
mem:?u32 = mem:?u32 with [R3:u32 ,e_little]:u32 =R2:u32
jmp  "pc_0x800"

addr 0x800 @asm  "ldr r2, [r1, #88]"
label pc_0x800
PC:u32 = 0x800:u32
tmp_r2:u32 = mem:?u32[(R1:u32 + low:u32(0x58:u64)),e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x804"

addr 0x804 @asm  "str r0, [r3, #60]"
label pc_0x804
PC:u32 = 0x804:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x3C:u64)) ,e_little]:u32 =R0:u32
jmp  "pc_0x808"

addr 0x808 @asm  "str r5, [r3, #64]"
label pc_0x808
PC:u32 = 0x808:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x40:u64)) ,e_little]:u32 =R5:u32
jmp  "pc_0x80C"

addr 0x80C @asm  "str r2, [r3, #52]"
label pc_0x80C
PC:u32 = 0x80C:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x34:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x810"

addr 0x810 @asm  "pop {r4-r6, pc}"
label pc_0x810
PC:u32 = 0x810:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x10:u64))
tmp_pc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r6:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r5:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x0:u64)),e_little]:u32
R4:u32 = tmp_r4:u32
R5:u32 = tmp_r5:u32
R6:u32 = tmp_r6:u32
PC:u32 = tmp_pc:u32
SP_SVC:u32 = tmp_sp_svc:u32
cjmp (PC<>0x68:u32), "lift_error", "pc_0x68"

jmp "lift_error"

PC:u32 = 0x810:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x10:u64))
tmp_r6:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r5:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
R4:u32 = tmp_r4:u32
R5:u32 = tmp_r5:u32
R6:u32 = tmp_r6:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp "lift_error"

addr 0x814 @asm  "ldr r0, [r3, #156]"
label pc_0x814
PC:u32 = 0x814:u32
tmp_r0:u32 = mem:?u32[(R3:u32 + low:u32(0x9C:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
tmp_cnd:bool = (false)
cjmp ~(tmp_cnd), "lift_error", "success"

jmp  "pc_0x818"

addr 0x818 @asm  "str r3, [r1]"
label pc_0x818
PC:u32 = 0x818:u32
mem:?u32 = mem:?u32 with [R1:u32 ,e_little]:u32 =R3:u32
jmp  "pc_0x81C"

addr 0x81C @asm  "ldr r3, [r0, #68]"
label pc_0x81C
PC:u32 = 0x81C:u32
tmp_r3:u32 = mem:?u32[(R0:u32 + low:u32(0x44:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x820"

addr 0x820 @asm  "ldr r4, [r3, #4]"
label pc_0x820
PC:u32 = 0x820:u32
tmp_r4:u32 = mem:?u32[(R3:u32 + low:u32(0x4:u64)),e_little]:u32
R4:u32 = tmp_r4:u32
jmp  "pc_0x824"

addr 0x824 @asm  "bl -#1512"
label pc_0x824
PC:u32 = 0x824:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x23C"

addr 0x828 @asm  "mov r0, r4"
label pc_0x828
PC:u32 = 0x828:u32
tmp_r0:u32 = R4:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x82C"

addr 0x82C @asm  "pop {r4-r6, lr}"
label pc_0x82C
PC:u32 = 0x82C:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x10:u64))
tmp_lr_svc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r6:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r5:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R4:u32 = tmp_r4:u32
R5:u32 = tmp_r5:u32
R6:u32 = tmp_r6:u32
SP_SVC:u32 = tmp_sp_svc:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x830"

addr 0x830 @asm  "b +#1176"
label pc_0x830
PC:u32 = 0x830:u32
jmp  "pc_0xCC8"

addr 0x834 @asm  "andeq r8, r0, r0, lsr r1"
label pc_0x834
PC:u32 = 0x834:u32
TmpV_59:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_59:bool , "L_117" , "pc_0x838"
label L_117
tmp_r8:u32 = (R0:u32 & (R0:u32 >> low:u32(extend:u64(R1:u32))))
R8:u32 = tmp_r8:u32
jmp  "pc_0x838"

addr 0x838 @asm  "andeq r1, r0, r5, asr #2"
label pc_0x838
PC:u32 = 0x838:u32
TmpV_60:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_60:bool , "L_119" , "pc_0x83C"
label L_119
tmp_r1:u32 = (R0:u32 & (R5:u32 $>> low:u32(0x2:u64)))
R1:u32 = tmp_r1:u32
jmp  "pc_0x83C"


addr 0x83C @asm  "push {r3, lr}"
label pc_0x83C
PC:u32 = 0x83C:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF8:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x840"

addr 0x840 @asm  "mov r3, r0"
label pc_0x840
PC:u32 = 0x840:u32
tmp_r3:u32 = R0:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x844"

addr 0x844 @asm  "mov r1, r2"
label pc_0x844
PC:u32 = 0x844:u32
tmp_r1:u32 = R2:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x848"

addr 0x848 @asm  "ldr r0, [pc, #16]"
label pc_0x848
PC:u32 = 0x848:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x18:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x84C"

addr 0x84C @asm  "mov r2, r3"
label pc_0x84C
PC:u32 = 0x84C:u32
tmp_r2:u32 = R3:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x850"

addr 0x850 @asm  "bl +#1548"
label pc_0x850
PC:u32 = 0x850:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32


addr 0x854 @asm  "bl -#448"
label pc_0x854
PC:u32 = 0x854:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x694"

addr 0x858 @asm  "mov r0, #0"
label pc_0x858
PC:u32 = 0x858:u32
tmp_r0:u32 = low:u32(0x0:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x85C"

addr 0x85C @asm  "pop {r3, pc}"
label pc_0x85C
PC:u32 = 0x85C:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x8:u64))
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp "lift_error"

addr 0x860 @asm  "andeq r1, r0, r9, asr r1"
label pc_0x860
PC:u32 = 0x860:u32
TmpV_61:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_61:bool , "L_121" , "pc_0x864"
label L_121
tmp_r1:u32 = (R0:u32 & (R9:u32 $>> low:u32(extend:u64(R1:u32))))
R1:u32 = tmp_r1:u32
jmp  "pc_0x864"


addr 0x864 @asm  "push {r4-r6, lr}"
label pc_0x864
PC:u32 = 0x864:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF0:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R6:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF4:u64)) ,e_little]:u32 =R5:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF0:u64)) ,e_little]:u32 =R4:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x868"

addr 0x868 @asm  "ldr r5, [pc, #52]"
label pc_0x868
PC:u32 = 0x868:u32
tmp_r5:u32 = mem:?u32[(PC:u32 + low:u32(0x3C:u64)),e_little]:u32
R5:u32 = tmp_r5:u32
jmp  "pc_0x86C"

addr 0x86C @asm  "ldr r3, [r5]"
label pc_0x86C
PC:u32 = 0x86C:u32
tmp_r3:u32 = mem:?u32[R5:u32,e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x870"

addr 0x870 @asm  "mov r4, r0"
label pc_0x870
PC:u32 = 0x870:u32
tmp_r4:u32 = R0:u32
R4:u32 = tmp_r4:u32
jmp  "pc_0x874"

addr 0x874 @asm  "mov r0, #72"
label pc_0x874
PC:u32 = 0x874:u32
tmp_r0:u32 = low:u32(0x48:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x878"

addr 0x878 @asm  "mla r0, r4, r0, r3"
label pc_0x878
PC:u32 = 0x878:u32
tmp_r0:u32 = ((R4:u32*R0:u32) + R3:u32)
R0:u32 = tmp_r0:u32
jmp  "pc_0x87C"

addr 0x87C @asm  "add r0, r0, #12"
label pc_0x87C
PC:u32 = 0x87C:u32
tmp_r0:u32 = (R0:u32 + low:u32(0xC:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0x880"

addr 0x880 @asm  "str r0, [r3, #156]"
label pc_0x880
PC:u32 = 0x880:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x9C:u64)) ,e_little]:u32 =R0:u32
jmp  "pc_0x884"

addr 0x884 @asm  "bl -#1608"
label pc_0x884
PC:u32 = 0x884:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x23C"

addr 0x888 @asm  "ldr r3, [r5]"
label pc_0x888
PC:u32 = 0x888:u32
tmp_r3:u32 = mem:?u32[R5:u32,e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x88C"

addr 0x88C @asm  "str r4, [r3, #4]"
label pc_0x88C
PC:u32 = 0x88C:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x4:u64)) ,e_little]:u32 =R4:u32
jmp  "pc_0x890"

addr 0x890 @asm  "ldr r3, [r3, #156]"
label pc_0x890
PC:u32 = 0x890:u32
tmp_r3:u32 = mem:?u32[(R3:u32 + low:u32(0x9C:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x894"

addr 0x894 @asm  "ldr r3, [r3, #68]"
label pc_0x894
PC:u32 = 0x894:u32
tmp_r3:u32 = mem:?u32[(R3:u32 + low:u32(0x44:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x898"

addr 0x898 @asm  "ldr r0, [r3, #4]"
label pc_0x898
PC:u32 = 0x898:u32
tmp_r0:u32 = mem:?u32[(R3:u32 + low:u32(0x4:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x89C"

addr 0x89C @asm  "pop {r4-r6, lr}"
label pc_0x89C
PC:u32 = 0x89C:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x10:u64))
tmp_lr_svc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r6:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r5:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R4:u32 = tmp_r4:u32
R5:u32 = tmp_r5:u32
R6:u32 = tmp_r6:u32
SP_SVC:u32 = tmp_sp_svc:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x8A0"

addr 0x8A0 @asm  "b +#1064"
label pc_0x8A0
PC:u32 = 0x8A0:u32
jmp  "pc_0xCC8"

addr 0x8A4 @asm  "andeq r8, r0, r0, lsr r1"
label pc_0x8A4
PC:u32 = 0x8A4:u32
TmpV_62:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_62:bool , "L_123" , "pc_0x8A8"
label L_123
tmp_r8:u32 = (R0:u32 & (R0:u32 >> low:u32(extend:u64(R1:u32))))
R8:u32 = tmp_r8:u32
jmp  "pc_0x8A8"


addr 0x8A8 @asm  "ldr r3, [pc, #20]"
label pc_0x8A8
PC:u32 = 0x8A8:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x1C:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x8AC"

addr 0x8AC @asm  "ldr r3, [r3]"
label pc_0x8AC
PC:u32 = 0x8AC:u32
tmp_r3:u32 = mem:?u32[R3:u32,e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x8B0"

addr 0x8B0 @asm  "ldr r3, [r3, #164]"
label pc_0x8B0
PC:u32 = 0x8B0:u32
tmp_r3:u32 = mem:?u32[(R3:u32 + low:u32(0xA4:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x8B4"

addr 0x8B4 @asm  "mov r2, #1"
label pc_0x8B4
PC:u32 = 0x8B4:u32
tmp_r2:u32 = low:u32(0x1:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x8B8"

addr 0x8B8 @asm  "str r2, [r3, #172]"
label pc_0x8B8
PC:u32 = 0x8B8:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xAC:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x8BC"

addr 0x8BC @asm  "str r0, [r3, #168]"
label pc_0x8BC
PC:u32 = 0x8BC:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xA8:u64)) ,e_little]:u32 =R0:u32
jmp  "pc_0x8C0"

addr 0x8C0 @asm  "mov pc, lr"
label pc_0x8C0
PC:u32 = 0x8C0:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x8C4 @asm  "andeq r8, r0, r0, lsr r1"
label pc_0x8C4
PC:u32 = 0x8C4:u32
TmpV_63:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_63:bool , "L_125" , "pc_0x8C8"
label L_125
tmp_r8:u32 = (R0:u32 & (R0:u32 >> low:u32(extend:u64(R1:u32))))
R8:u32 = tmp_r8:u32
jmp  "pc_0x8C8"


addr 0x8C8 @asm  "ldr r3, [pc, #24]"
label pc_0x8C8
PC:u32 = 0x8C8:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x20:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x8CC"

addr 0x8CC @asm  "ldr r3, [r3]"
label pc_0x8CC
PC:u32 = 0x8CC:u32
tmp_r3:u32 = mem:?u32[R3:u32,e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x8D0"

addr 0x8D0 @asm  "ldr r3, [r3, #156]"
label pc_0x8D0
PC:u32 = 0x8D0:u32
tmp_r3:u32 = mem:?u32[(R3:u32 + low:u32(0x9C:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x8D4"

addr 0x8D4 @asm  "ldr r2, [r3, #60]"
label pc_0x8D4
PC:u32 = 0x8D4:u32
tmp_r2:u32 = mem:?u32[(R3:u32 + low:u32(0x3C:u64)),e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x8D8"

addr 0x8D8 @asm  "mov r1, r0"
label pc_0x8D8
PC:u32 = 0x8D8:u32
tmp_r1:u32 = R0:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x8DC"

addr 0x8DC @asm  "ldr r0, [pc, #8]"
label pc_0x8DC
PC:u32 = 0x8DC:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x10:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x8E0"

addr 0x8E0 @asm  "sub r2, r2, #4"
label pc_0x8E0
PC:u32 = 0x8E0:u32
tmp_r2:u32 = (R2:u32 + low:u32(0xFFFFFFFC:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0x8E4"

addr 0x8E4 @asm  "b +#1400"
label pc_0x8E4
PC:u32 = 0x8E4:u32


addr 0x8E8 @asm  "andeq r8, r0, r0, lsr r1"
label pc_0x8E8
PC:u32 = 0x8E8:u32
TmpV_64:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_64:bool , "L_127" , "pc_0x8EC"
label L_127
tmp_r8:u32 = (R0:u32 & (R0:u32 >> low:u32(extend:u64(R1:u32))))
R8:u32 = tmp_r8:u32
jmp  "pc_0x8EC"

addr 0x8EC @asm  "andeq r1, r0, r6, lsl #3"
label pc_0x8EC
PC:u32 = 0x8EC:u32
TmpV_65:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_65:bool , "L_129" , "pc_0x8F0"
label L_129
tmp_r1:u32 = (R0:u32 & (R6:u32 << low:u32(0x3:u64)))
R1:u32 = tmp_r1:u32
jmp  "pc_0x8F0"


addr 0x8F0 @asm  "mov r1, r0"
label pc_0x8F0
PC:u32 = 0x8F0:u32
tmp_r1:u32 = R0:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x8F4"

addr 0x8F4 @asm  "ldr r0, [pc, #-0]"
label pc_0x8F4
PC:u32 = 0x8F4:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x8:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x8F8"

addr 0x8F8 @asm  "b +#1380"
label pc_0x8F8
PC:u32 = 0x8F8:u32


addr 0x8FC @asm  "strheq r1, [r0], -r8"
label pc_0x8FC
PC:u32 = 0x8FC:u32
jmp "lift_error"
cjmp TmpV_66:bool , "L_131" , "pc_0x900"
label L_131
tmp_r0:u32 = (R0:u32 +  -R8:u32)
mem:?u32 = mem:?u32 with [R0:u32 ,e_little]:u16 = (low:u16(R1:u32))R0:u32 = tmp_r0:u32
jmp  "pc_0x900"


addr 0x900 @asm  "push {r4, lr}"
label pc_0x900
PC:u32 = 0x900:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF8:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R4:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x904"

addr 0x904 @asm  "ldr r4, [pc, #92]"
label pc_0x904
PC:u32 = 0x904:u32
tmp_r4:u32 = mem:?u32[(PC:u32 + low:u32(0x64:u64)),e_little]:u32
R4:u32 = tmp_r4:u32
jmp  "pc_0x908"

addr 0x908 @asm  "ldr r3, [r4]"
label pc_0x908
PC:u32 = 0x908:u32
tmp_r3:u32 = mem:?u32[R4:u32,e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x90C"

addr 0x90C @asm  "ldr r1, [r3, #160]"
label pc_0x90C
PC:u32 = 0x90C:u32
tmp_r1:u32 = mem:?u32[(R3:u32 + low:u32(0xA0:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x910"

addr 0x910 @asm  "ldr r2, [r3, #4]"
label pc_0x910
PC:u32 = 0x910:u32
tmp_r2:u32 = mem:?u32[(R3:u32 + low:u32(0x4:u64)),e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x914"

addr 0x914 @asm  "ldr r1, [r1, #84]"
label pc_0x914
PC:u32 = 0x914:u32
tmp_r1:u32 = mem:?u32[(R1:u32 + low:u32(0x54:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x918"

addr 0x918 @asm  "cmp r2, r1"
label pc_0x918
PC:u32 = 0x918:u32
tmp_n_flag:bool = low:bool(low:bool(((R2:u32 +  -R1:u32)) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R2:u32) + extend:u64( ~R1:u32) + 0x1:u64) < 0x100000000:u64 then (extend:u64(R2:u32) + extend:u64( ~R1:u32) + 0x1:u64) else ((extend:u64(R2:u32) + extend:u64( ~R1:u32) + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R2:u32) + extend:u64( ~R1:u32) + 0x1:u64)))
tmp_z_flag:bool = low:bool((R2:u32 == R1:u32))
tmp_v_flag:bool = low:bool((low:bool((R2:u32) >> 0x1f:u32 ) == low:bool(( ~R1:u32) >> 0x1f:u32 )) & ~(low:bool((R2:u32) >> 0x1f:u32 ) == ((((extend:u64(R2:u32) + extend:u64( ~R1:u32) + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x91C"

addr 0x91C @asm  "ldrne r0, [pc, #72]"
label pc_0x91C
PC:u32 = 0x91C:u32
TmpV_67:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_67:bool , "L_133" , "pc_0x920"
label L_133
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x50:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x920"

addr 0x920 @asm  "movne r1, #1"
label pc_0x920
PC:u32 = 0x920:u32
TmpV_68:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_68:bool , "L_135" , "pc_0x924"
label L_135
tmp_r1:u32 = low:u32(0x1:u64)
R1:u32 = tmp_r1:u32
jmp  "pc_0x924"

addr 0x924 @asm  "bne +#40"
label pc_0x924
PC:u32 = 0x924:u32
TmpV_69:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_69:bool , "pc_0x94C" , "pc_0x928"

addr 0x928 @asm  "ldr r0, [r3, #8]"
label pc_0x928
PC:u32 = 0x928:u32
tmp_r0:u32 = mem:?u32[(R3:u32 + low:u32(0x8:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x92C"

addr 0x92C @asm  "cmp r0, #1"
label pc_0x92C
PC:u32 = 0x92C:u32
tmp_n_flag:bool = low:bool(low:bool(((R0:u32 + low:u32(0xFFFFFFFF:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R0:u32 + low:u32(0xFFFFFFFF:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x930"

addr 0x930 @asm  "ldrhi r0, [pc, #56]"
label pc_0x930

jmp "lift_error"

addr 0x934 @asm  "movhi r1, #2"
label pc_0x934
PC:u32 = 0x934:u32
TmpV_70:bool = low:bool( C_FLAG:bool & ~Z_FLAG:bool)
cjmp TmpV_70:bool , "L_139" , "pc_0x938"
label L_139
tmp_r1:u32 = low:u32(0x2:u64)
R1:u32 = tmp_r1:u32
jmp  "pc_0x938"

addr 0x938 @asm  "bhi +#20"
label pc_0x938
PC:u32 = 0x938:u32
TmpV_71:bool = low:bool( C_FLAG:bool & ~Z_FLAG:bool)
cjmp TmpV_71:bool , "pc_0x94C" , "pc_0x93C"

addr 0x93C @asm  "cmp r0, r2"
label pc_0x93C
PC:u32 = 0x93C:u32
tmp_n_flag:bool = low:bool(low:bool(((R0:u32 +  -R2:u32)) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64) else ((extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == R2:u32))
tmp_v_flag:bool = low:bool((low:bool((R0:u32) >> 0x1f:u32 ) == low:bool(( ~R2:u32) >> 0x1f:u32 )) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x940"

addr 0x940 @asm  "bne +#20"
label pc_0x940
PC:u32 = 0x940:u32
TmpV_72:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_72:bool , "pc_0x954" , "pc_0x944"

addr 0x944 @asm  "ldr r0, [pc, #40]"
label pc_0x944
PC:u32 = 0x944:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x30:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x948"

addr 0x948 @asm  "mov r1, #3"
label pc_0x948
PC:u32 = 0x948:u32
tmp_r1:u32 = low:u32(0x3:u64)
R1:u32 = tmp_r1:u32
jmp  "pc_0x94C"

addr 0x94C @asm  "pop {r4, lr}"
label pc_0x94C
PC:u32 = 0x94C:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x8:u64))
tmp_lr_svc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R4:u32 = tmp_r4:u32
SP_SVC:u32 = tmp_sp_svc:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x950"

addr 0x950 @asm  "b -#96"
label pc_0x950
PC:u32 = 0x950:u32
jmp  "pc_0x8F0"

addr 0x954 @asm  "bl -#240"
label pc_0x954
PC:u32 = 0x954:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x864"

addr 0x958 @asm  "ldr r3, [r4]"
label pc_0x958
PC:u32 = 0x958:u32
tmp_r3:u32 = mem:?u32[R4:u32,e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x95C"

addr 0x95C @asm  "mvn r2, #0"
label pc_0x95C
PC:u32 = 0x95C:u32
tmp_r2:u32 = low:u32(0xFFFFFFFF:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x960"

addr 0x960 @asm  "str r2, [r3, #8]"
label pc_0x960
PC:u32 = 0x960:u32
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0x8:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0x964"

addr 0x964 @asm  "pop {r4, pc}"
label pc_0x964
PC:u32 = 0x964:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x8:u64))
tmp_r4:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
R4:u32 = tmp_r4:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp "lift_error"

addr 0x968 @asm  "andeq r8, r0, r0, lsr r1"
label pc_0x968
PC:u32 = 0x968:u32
TmpV_73:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_73:bool , "L_145" , "pc_0x96C"
label L_145
tmp_r8:u32 = (R0:u32 & (R0:u32 >> low:u32(extend:u64(R1:u32))))
R8:u32 = tmp_r8:u32
jmp  "pc_0x96C"

addr 0x96C @asm  "andeq r1, r0, r1, lsr #4"
label pc_0x96C
PC:u32 = 0x96C:u32
TmpV_74:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_74:bool , "L_147" , "pc_0x970"
label L_147
tmp_r1:u32 = (R0:u32 & (R1:u32 >> low:u32(0x4:u64)))
R1:u32 = tmp_r1:u32
jmp  "pc_0x970"

addr 0x970 @asm  "andeq r1, r0, r9, asr r2"
label pc_0x970
PC:u32 = 0x970:u32
TmpV_75:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_75:bool , "L_149" , "pc_0x974"
label L_149
tmp_r1:u32 = (R0:u32 & (R9:u32 $>> low:u32(extend:u64(R2:u32))))
R1:u32 = tmp_r1:u32
jmp  "pc_0x974"

addr 0x974 @asm  "andeq r1, r0, r9, ror r2"
label pc_0x974
PC:u32 = 0x974:u32
TmpV_76:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_76:bool , "L_151" , "pc_0x978"
label L_151
jmp "lift_error"
R1:u32 = tmp_r1:u32
jmp  "pc_0x978"


addr 0x978 @asm  "push {r0-r2, r4-r7, lr}"
label pc_0x978
PC:u32 = 0x978:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFE0:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R7:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF4:u64)) ,e_little]:u32 =R6:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF0:u64)) ,e_little]:u32 =R5:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFEC:u64)) ,e_little]:u32 =R4:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFE8:u64)) ,e_little]:u32 =R2:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFE4:u64)) ,e_little]:u32 =R1:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFE0:u64)) ,e_little]:u32 =R0:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x97C"

addr 0x97C @asm  "add r0, sp, #7"
label pc_0x97C
PC:u32 = 0x97C:u32
tmp_r0:u32 = (SP_SVC:u32 + low:u32(0x7:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0x980"

addr 0x980 @asm  "add r1, sp, #6"
label pc_0x980
PC:u32 = 0x980:u32
tmp_r1:u32 = (SP_SVC:u32 + low:u32(0x6:u64))
R1:u32 = tmp_r1:u32
jmp  "pc_0x984"

addr 0x984 @asm  "bl -#1812"
label pc_0x984
PC:u32 = 0x984:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x270"

addr 0x988 @asm  "mov r4, #0"
label pc_0x988
PC:u32 = 0x988:u32
tmp_r4:u32 = low:u32(0x0:u64)
R4:u32 = tmp_r4:u32
jmp  "pc_0x98C"

addr 0x98C @asm  "ldr r7, [pc, #192]"
label pc_0x98C
PC:u32 = 0x98C:u32
tmp_r7:u32 = mem:?u32[(PC:u32 + low:u32(0xC8:u64)),e_little]:u32
R7:u32 = tmp_r7:u32
jmp  "pc_0x990"

addr 0x990 @asm  "mov r5, r4"
label pc_0x990
PC:u32 = 0x990:u32
tmp_r5:u32 = R4:u32
R5:u32 = tmp_r5:u32
jmp  "pc_0x994"

addr 0x994 @asm  "mov r6, r5, lsl #20"
label pc_0x994
PC:u32 = 0x994:u32
tmp_r6:u32 = (R5:u32 << low:u32(0x14:u64))
R6:u32 = tmp_r6:u32
jmp  "pc_0x998"

addr 0x998 @asm  "mov r0, r6"
label pc_0x998
PC:u32 = 0x998:u32
tmp_r0:u32 = R6:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x99C"

addr 0x99C @asm  "bl +#560"
label pc_0x99C
PC:u32 = 0x99C:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xBCC"

addr 0x9A0 @asm  "cmp r0, #0"
label pc_0x9A0
PC:u32 = 0x9A0:u32
tmp_n_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x9A4"

addr 0x9A4 @asm  "ldrne r0, [r0, #8]"
label pc_0x9A4
PC:u32 = 0x9A4:u32
jmp "lift_error"
cjmp TmpV_77:bool , "L_153" , "pc_0x9A8"
label L_153
tmp_r0:u32 = mem:?u32[(R0:u32 + low:u32(0x8:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x9A8"

addr 0x9A8 @asm  "sub r3, r0, #1"
label pc_0x9A8
PC:u32 = 0x9A8:u32
tmp_r3:u32 = (R0:u32 + low:u32(0xFFFFFFFF:u64))
R3:u32 = tmp_r3:u32
jmp  "pc_0x9AC"

addr 0x9AC @asm  "cmp r3, #5"
label pc_0x9AC
PC:u32 = 0x9AC:u32
tmp_n_flag:bool = low:bool(low:bool(((R3:u32 + low:u32(0xFFFFFFFB:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R3:u32) + 0xFFFFFFFA:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R3:u32) + 0xFFFFFFFA:u64 + 0x1:u64) else ((extend:u64(R3:u32) + 0xFFFFFFFA:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R3:u32) + 0xFFFFFFFA:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R3:u32 + low:u32(0xFFFFFFFB:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R3:u32) >> 0x1f:u32 ) & ~(low:bool((R3:u32) >> 0x1f:u32 ) == ((((extend:u64(R3:u32) + 0xFFFFFFFA:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x9B0"

addr 0x9B0 @asm  "ldrls r1, [pc, #160]"
label pc_0x9B0
PC:u32 = 0x9B0:u32
jmp "lift_error"
cjmp TmpV_78:bool , "L_155" , "pc_0x9B4"
label L_155
tmp_r1:u32 = mem:?u32[(PC:u32 + low:u32(0xA8:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x9B4"

addr 0x9B4 @asm  "ldrls r2, [r1, r3, lsl #2]"
label pc_0x9B4
PC:u32 = 0x9B4:u32
jmp "lift_error"
cjmp TmpV_79:bool , "L_157" , "pc_0x9B8"
label L_157
tmp_r2:u32 = mem:?u32[(R1:u32 + (R3:u32 << low:u32(0x2:u64))),e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x9B8"

addr 0x9B8 @asm  "addls r3, r1, r3, lsl #2"
label pc_0x9B8
PC:u32 = 0x9B8:u32
jmp "lift_error"
cjmp TmpV_80:bool , "L_159" , "pc_0x9BC"
label L_159
tmp_r3:u32 = (R1:u32 + (R3:u32 << low:u32(0x2:u64)))
R3:u32 = tmp_r3:u32
jmp  "pc_0x9BC"

addr 0x9BC @asm  "ldrb r1, [sp, #7]"
label pc_0x9BC
PC:u32 = 0x9BC:u32
r1:u32 = pad:u32(mem:?u32[(SP_SVC:u32 + low:u32(0x7:u64)) ,e_little]:u8)
R1:u32 = tmp_r1:u32
jmp  "pc_0x9C0"

addr 0x9C0 @asm  "ldrls r3, [r3, #24]"
label pc_0x9C0
PC:u32 = 0x9C0:u32
jmp "lift_error"
cjmp TmpV_81:bool , "L_161" , "pc_0x9C4"
label L_161
tmp_r3:u32 = mem:?u32[(R3:u32 + low:u32(0x18:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x9C4"

addr 0x9C4 @asm  "movhi r3, #0"
label pc_0x9C4
PC:u32 = 0x9C4:u32
TmpV_82:bool = low:bool( C_FLAG:bool & ~Z_FLAG:bool)
cjmp TmpV_82:bool , "L_163" , "pc_0x9C8"
label L_163
tmp_r3:u32 = low:u32(0x0:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x9C8"

addr 0x9C8 @asm  "movhi r2, #2"
label pc_0x9C8
PC:u32 = 0x9C8:u32
TmpV_83:bool = low:bool( C_FLAG:bool & ~Z_FLAG:bool)
cjmp TmpV_83:bool , "L_165" , "pc_0x9CC"
label L_165
tmp_r2:u32 = low:u32(0x2:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x9CC"

addr 0x9CC @asm  "cmp r1, #0"
label pc_0x9CC
PC:u32 = 0x9CC:u32
tmp_n_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R1:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x9D0"

addr 0x9D0 @asm  "bne +#76"
label pc_0x9D0
PC:u32 = 0x9D0:u32
TmpV_84:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_84:bool , "pc_0xA1C" , "pc_0x9D4"

addr 0x9D4 @asm  "ldrb r1, [sp, #6]"
label pc_0x9D4
PC:u32 = 0x9D4:u32
r1:u32 = pad:u32(mem:?u32[(SP_SVC:u32 + low:u32(0x6:u64)) ,e_little]:u8)
R1:u32 = tmp_r1:u32
jmp  "pc_0x9D8"

addr 0x9D8 @asm  "cmp r1, #0"
label pc_0x9D8
PC:u32 = 0x9D8:u32
tmp_n_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R1:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x9DC"

addr 0x9DC @asm  "orreq r4, r6, #18"
label pc_0x9DC
PC:u32 = 0x9DC:u32
TmpV_85:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_85:bool , "L_169" , "pc_0x9E0"
label L_169
tmp_r4:u32 = R6:u32 | low:u32(0x12:u64)
R4:u32 = tmp_r4:u32
jmp  "pc_0x9E0"

addr 0x9E0 @asm  "orreq r4, r4, r2, lsl #5"
label pc_0x9E0
PC:u32 = 0x9E0:u32
TmpV_86:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_86:bool , "L_171" , "pc_0x9E4"
label L_171
tmp_r4:u32 = R4:u32 | (R2:u32 << low:u32(0x5:u64))
R4:u32 = tmp_r4:u32
jmp  "pc_0x9E4"

addr 0x9E4 @asm  "orreq r4, r4, r3, lsl #10"
label pc_0x9E4
PC:u32 = 0x9E4:u32
TmpV_87:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_87:bool , "L_173" , "pc_0x9E8"
label L_173
tmp_r4:u32 = R4:u32 | (R3:u32 << low:u32(0xA:u64))
R4:u32 = tmp_r4:u32
jmp  "pc_0x9E8"

addr 0x9E8 @asm  "beq +#52"
label pc_0x9E8
PC:u32 = 0x9E8:u32
TmpV_88:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_88:bool , "pc_0xA1C" , "pc_0x9EC"

addr 0x9EC @asm  "cmp r1, #2"
label pc_0x9EC
PC:u32 = 0x9EC:u32
tmp_n_flag:bool = low:bool(low:bool(((R1:u32 + low:u32(0xFFFFFFFE:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFFFFFD:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFFFFFD:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFFFFFD:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFFFFFD:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R1:u32 + low:u32(0xFFFFFFFE:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFFFFFD:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x9F0"

addr 0x9F0 @asm  "bne +#44"
label pc_0x9F0
PC:u32 = 0x9F0:u32
TmpV_89:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_89:bool , "pc_0xA1C" , "pc_0x9F4"

addr 0x9F4 @asm  "orr r4, r6, #18"
label pc_0x9F4
PC:u32 = 0x9F4:u32
tmp_r4:u32 = R6:u32 | low:u32(0x12:u64)
R4:u32 = tmp_r4:u32
jmp  "pc_0x9F8"

addr 0x9F8 @asm  "orr r4, r4, r2, lsl #5"
label pc_0x9F8
PC:u32 = 0x9F8:u32
tmp_r4:u32 = R4:u32 | (R2:u32 << low:u32(0x5:u64))
R4:u32 = tmp_r4:u32
jmp  "pc_0x9FC"

addr 0x9FC @asm  "cmp r0, #1"
label pc_0x9FC
PC:u32 = 0x9FC:u32
tmp_n_flag:bool = low:bool(low:bool(((R0:u32 + low:u32(0xFFFFFFFF:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R0:u32 + low:u32(0xFFFFFFFF:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xA00"

addr 0xA00 @asm  "cmpne r0, #3"
label pc_0xA00
PC:u32 = 0xA00:u32
TmpV_90:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_90:bool , "L_179" , "pc_0xA04"
label L_179
tmp_n_flag:bool = low:bool(low:bool(((R0:u32 + low:u32(0xFFFFFFFD:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFC:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFC:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFC:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFC:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R0:u32 + low:u32(0xFFFFFFFD:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFC:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xA04"

addr 0xA04 @asm  "orr r4, r4, r3, lsl #10"
label pc_0xA04
PC:u32 = 0xA04:u32
tmp_r4:u32 = R4:u32 | (R3:u32 << low:u32(0xA:u64))
R4:u32 = tmp_r4:u32
jmp  "pc_0xA08"

addr 0xA08 @asm  "beq +#12"
label pc_0xA08
PC:u32 = 0xA08:u32
TmpV_91:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_91:bool , "pc_0xA14" , "pc_0xA0C"

addr 0xA0C @asm  "cmp r0, #4"
label pc_0xA0C
PC:u32 = 0xA0C:u32
tmp_n_flag:bool = low:bool(low:bool(((R0:u32 + low:u32(0xFFFFFFFC:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFB:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFB:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFB:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFB:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R0:u32 + low:u32(0xFFFFFFFC:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFB:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xA10"

addr 0xA10 @asm  "bne +#12"
label pc_0xA10
PC:u32 = 0xA10:u32
TmpV_92:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_92:bool , "pc_0xA1C" , "pc_0xA14"

addr 0xA14 @asm  "bic r4, r4, #28"
label pc_0xA14
PC:u32 = 0xA14:u32
tmp_r4:u32 = (R4:u32 & low:u32(0xFFFFFFE3:u64))
R4:u32 = tmp_r4:u32
jmp  "pc_0xA18"

addr 0xA18 @asm  "orr r4, r4, #12"
label pc_0xA18
PC:u32 = 0xA18:u32
tmp_r4:u32 = R4:u32 | low:u32(0xC:u64)
R4:u32 = tmp_r4:u32
jmp  "pc_0xA1C"

addr 0xA1C @asm  "add r5, r5, #1"
label pc_0xA1C
PC:u32 = 0xA1C:u32
tmp_r5:u32 = (R5:u32 + low:u32(0x1:u64))
R5:u32 = tmp_r5:u32
jmp  "pc_0xA20"

addr 0xA20 @asm  "cmp r5, #4096"
label pc_0xA20
PC:u32 = 0xA20:u32
tmp_n_flag:bool = low:bool(low:bool(((R5:u32 + low:u32(0xFFFFF000:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R5:u32) + 0xFFFFEFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R5:u32) + 0xFFFFEFFF:u64 + 0x1:u64) else ((extend:u64(R5:u32) + 0xFFFFEFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R5:u32) + 0xFFFFEFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R5:u32 + low:u32(0xFFFFF000:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R5:u32) >> 0x1f:u32 ) & ~(low:bool((R5:u32) >> 0x1f:u32 ) == ((((extend:u64(R5:u32) + 0xFFFFEFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xA24"

addr 0xA24 @asm  "str r4, [r7, #4]!"
label pc_0xA24
PC:u32 = 0xA24:u32
tmp_r7:u32 = (R7:u32 + low:u32(0x4:u64))
mem:?u32 = mem:?u32 with [(R7:u32 + low:u32(0x4:u64)) ,e_little]:u32 =R4:u32
R7:u32 = tmp_r7:u32
jmp  "pc_0xA28"

addr 0xA28 @asm  "bne -#148"
label pc_0xA28
PC:u32 = 0xA28:u32
TmpV_93:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_93:bool , "pc_0x994" , "pc_0xA2C"

addr 0xA2C @asm  "ldr r0, [pc, #40]"
label pc_0xA2C
PC:u32 = 0xA2C:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x30:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xA30"

addr 0xA30 @asm  "bl +#664"
label pc_0xA30
PC:u32 = 0xA30:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xCC8"

addr 0xA34 @asm  "ldr r0, [pc, #36]"
label pc_0xA34
PC:u32 = 0xA34:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x2C:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xA38"

addr 0xA38 @asm  "bl +#664"
label pc_0xA38
PC:u32 = 0xA38:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xCD0"

addr 0xA3C @asm  "mov r0, #1"
label pc_0xA3C
PC:u32 = 0xA3C:u32
tmp_r0:u32 = low:u32(0x1:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0xA40"

addr 0xA40 @asm  "mov r1, r0"
label pc_0xA40
PC:u32 = 0xA40:u32
tmp_r1:u32 = R0:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0xA44"

addr 0xA44 @asm  "bl -#1896"
label pc_0xA44
PC:u32 = 0xA44:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x2DC"

addr 0xA48 @asm  "mov r0, #1"
label pc_0xA48
PC:u32 = 0xA48:u32
tmp_r0:u32 = low:u32(0x1:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0xA4C"

addr 0xA4C @asm  "bl +#652"
label pc_0xA4C
PC:u32 = 0xA4C:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xCD8"

addr 0xA50 @asm  "pop {r1-r7, pc}"
label pc_0xA50
PC:u32 = 0xA50:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x20:u64))
tmp_r7:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x1C:u64)),e_little]:u32
tmp_r6:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x18:u64)),e_little]:u32
tmp_r5:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x14:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x10:u64)),e_little]:u32
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r2:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r1:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
R2:u32 = tmp_r2:u32
R3:u32 = tmp_r3:u32
R4:u32 = tmp_r4:u32
R5:u32 = tmp_r5:u32
R6:u32 = tmp_r6:u32
R7:u32 = tmp_r7:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp "lift_error"

addr 0xA54 @asm  "strdeq r3, r4, [r0], -r12"
label pc_0xA54

jmp "lift_error"

addr 0xA58 @asm  "andeq r1, r0, r12, ror #6"
label pc_0xA58
PC:u32 = 0xA58:u32
TmpV_94:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_94:bool , "L_187" , "pc_0xA5C"
label L_187
jmp "lift_error"
R1:u32 = tmp_r1:u32
jmp  "pc_0xA5C"

addr 0xA5C @asm  "ldrbpl r5, [r5, #-1365]"
label pc_0xA5C
PC:u32 = 0xA5C:u32
TmpV_95:bool = low:bool( ~N_FLAG:bool)
cjmp TmpV_95:bool , "L_189" , "pc_0xA60"
label L_189
r5:u32 = pad:u32(mem:?u32[(R5:u32 + low:u32(0xFFFFFAAB:u64)) ,e_little]:u8)
R5:u32 = tmp_r5:u32
jmp  "pc_0xA60"

addr 0xA60 @asm  "andeq r4, r0, r0"
label pc_0xA60
PC:u32 = 0xA60:u32
TmpV_96:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_96:bool , "L_191" , "pc_0xA64"
label L_191
tmp_r4:u32 = R0:u32
R4:u32 = tmp_r4:u32
jmp  "pc_0xA64"


addr 0xA64 @asm  "push {r4, lr}"
label pc_0xA64
PC:u32 = 0xA64:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF8:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R4:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xA68"

addr 0xA68 @asm  "ldr r1, [pc, #32]"
label pc_0xA68
PC:u32 = 0xA68:u32
tmp_r1:u32 = mem:?u32[(PC:u32 + low:u32(0x28:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0xA6C"

addr 0xA6C @asm  "ldr r0, [pc, #32]"
label pc_0xA6C
PC:u32 = 0xA6C:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x28:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xA70"

addr 0xA70 @asm  "bl -#2032"
label pc_0xA70
PC:u32 = 0xA70:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x280"

addr 0xA74 @asm  "ldr r0, [pc, #28]"
label pc_0xA74
PC:u32 = 0xA74:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x24:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xA78"

addr 0xA78 @asm  "bl -#2024"
label pc_0xA78
PC:u32 = 0xA78:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x290"

addr 0xA7C @asm  "ldr r0, [pc, #24]"
label pc_0xA7C
PC:u32 = 0xA7C:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x20:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xA80"

addr 0xA80 @asm  "bl -#2016"
label pc_0xA80
PC:u32 = 0xA80:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x2A0"

addr 0xA84 @asm  "ldr r0, [pc, #20]"
label pc_0xA84
PC:u32 = 0xA84:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x1C:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xA88"

addr 0xA88 @asm  "pop {r4, lr}"
label pc_0xA88
PC:u32 = 0xA88:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x8:u64))
tmp_lr_svc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R4:u32 = tmp_r4:u32
SP_SVC:u32 = tmp_sp_svc:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xA8C"

addr 0xA8C @asm  "b -#1392"
label pc_0xA8C
PC:u32 = 0xA8C:u32
jmp  "pc_0x51C"

addr 0xA90 @asm  "andeq r0, r0, r8, asr r7"
label pc_0xA90
PC:u32 = 0xA90:u32
TmpV_97:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_97:bool , "L_193" , "pc_0xA94"
label L_193
tmp_r0:u32 = (R0:u32 & (R8:u32 $>> low:u32(extend:u64(R7:u32))))
R0:u32 = tmp_r0:u32
jmp  "pc_0xA94"

addr 0xA94 @asm  "andeq r0, r0, r0, lsr r7"
label pc_0xA94
PC:u32 = 0xA94:u32
TmpV_98:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_98:bool , "L_195" , "pc_0xA98"
label L_195
tmp_r0:u32 = (R0:u32 & (R0:u32 >> low:u32(extend:u64(R7:u32))))
R0:u32 = tmp_r0:u32
jmp  "pc_0xA98"

addr 0xA98 @asm  "andeq r0, r0, r4, ror #13"
label pc_0xA98
PC:u32 = 0xA98:u32
TmpV_99:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_99:bool , "L_197" , "pc_0xA9C"
label L_197
jmp "lift_error"
R0:u32 = tmp_r0:u32
jmp  "pc_0xA9C"

addr 0xA9C @asm  "andeq r0, r0, r12, lsr r8"
label pc_0xA9C
PC:u32 = 0xA9C:u32
TmpV_100:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_100:bool , "L_199" , "pc_0xAA0"
label L_199
tmp_r0:u32 = (R0:u32 & (R12:u32 >> low:u32(extend:u64(R8:u32))))
R0:u32 = tmp_r0:u32
jmp  "pc_0xAA0"

addr 0xAA0 @asm  "andeq r0, r0, r0, lsl #15"
label pc_0xAA0
PC:u32 = 0xAA0:u32
TmpV_101:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_101:bool , "L_201" , "pc_0xAA4"
label L_201
tmp_r0:u32 = (R0:u32 & (R0:u32 << low:u32(0xF:u64)))
R0:u32 = tmp_r0:u32
jmp  "pc_0xAA4"


addr 0xAA4 @asm  "ldr r0, [pc, #172]"
label pc_0xAA4
PC:u32 = 0xAA4:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0xB4:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xAA8"

addr 0xAA8 @asm  "ldr r1, [pc, #172]"
label pc_0xAA8
PC:u32 = 0xAA8:u32
tmp_r1:u32 = mem:?u32[(PC:u32 + low:u32(0xB4:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0xAAC"

addr 0xAAC @asm  "ldr r2, [pc, #172]"
label pc_0xAAC
PC:u32 = 0xAAC:u32
tmp_r2:u32 = mem:?u32[(PC:u32 + low:u32(0xB4:u64)),e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0xAB0"

addr 0xAB0 @asm  "str r1, [r0, #160]"
label pc_0xAB0
PC:u32 = 0xAB0:u32
mem:?u32 = mem:?u32 with [(R0:u32 + low:u32(0xA0:u64)) ,e_little]:u32 =R1:u32
jmp  "pc_0xAB4"

addr 0xAB4 @asm  "mov r12, #1"
label pc_0xAB4
PC:u32 = 0xAB4:u32
tmp_r12:u32 = low:u32(0x1:u64)
R12:u32 = tmp_r12:u32
jmp  "pc_0xAB8"

addr 0xAB8 @asm  "add r1, r1, #108"
label pc_0xAB8
PC:u32 = 0xAB8:u32
tmp_r1:u32 = (R1:u32 + low:u32(0x6C:u64))
R1:u32 = tmp_r1:u32
jmp  "pc_0xABC"

addr 0xABC @asm  "str r12, [r2]"
label pc_0xABC
PC:u32 = 0xABC:u32
mem:?u32 = mem:?u32 with [R2:u32 ,e_little]:u32 =R12:u32
jmp  "pc_0xAC0"

addr 0xAC0 @asm  "str r2, [r0, #164]"
label pc_0xAC0
PC:u32 = 0xAC0:u32
mem:?u32 = mem:?u32 with [(R0:u32 + low:u32(0xA4:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0xAC4"

addr 0xAC4 @asm  "str r0, [r2, #164]"
label pc_0xAC4
PC:u32 = 0xAC4:u32
mem:?u32 = mem:?u32 with [(R2:u32 + low:u32(0xA4:u64)) ,e_little]:u32 =R0:u32
jmp  "pc_0xAC8"

addr 0xAC8 @asm  "str r1, [r2, #160]"
label pc_0xAC8
PC:u32 = 0xAC8:u32
mem:?u32 = mem:?u32 with [(R2:u32 + low:u32(0xA0:u64)) ,e_little]:u32 =R1:u32
jmp  "pc_0xACC"

addr 0xACC @asm  "ldr r2, [pc, #144]"
label pc_0xACC
PC:u32 = 0xACC:u32
tmp_r2:u32 = mem:?u32[(PC:u32 + low:u32(0x98:u64)),e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0xAD0"

addr 0xAD0 @asm  "mov r3, #0"
label pc_0xAD0
PC:u32 = 0xAD0:u32
tmp_r3:u32 = low:u32(0x0:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0xAD4"

addr 0xAD4 @asm  "str r3, [r0]"
label pc_0xAD4
PC:u32 = 0xAD4:u32
mem:?u32 = mem:?u32 with [R0:u32 ,e_little]:u32 =R3:u32
jmp  "pc_0xAD8"

addr 0xAD8 @asm  "str r0, [r2]"
label pc_0xAD8
PC:u32 = 0xAD8:u32
mem:?u32 = mem:?u32 with [R2:u32 ,e_little]:u32 =R0:u32
jmp  "pc_0xADC"

addr 0xADC @asm  "b +#36"
label pc_0xADC
PC:u32 = 0xADC:u32
jmp  "pc_0xB00"

addr 0xAE0 @asm  "add r2, r3, #1"
label pc_0xAE0
PC:u32 = 0xAE0:u32
tmp_r2:u32 = (R3:u32 + low:u32(0x1:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0xAE4"

addr 0xAE4 @asm  "mov r1, #72"
label pc_0xAE4
PC:u32 = 0xAE4:u32
tmp_r1:u32 = low:u32(0x48:u64)
R1:u32 = tmp_r1:u32
jmp  "pc_0xAE8"

addr 0xAE8 @asm  "mla r1, r2, r1, r0"
label pc_0xAE8
PC:u32 = 0xAE8:u32
tmp_r1:u32 = ((R2:u32*R1:u32) + R0:u32)
R1:u32 = tmp_r1:u32
jmp  "pc_0xAEC"

addr 0xAEC @asm  "ldr r12, [r0, #160]"
label pc_0xAEC
PC:u32 = 0xAEC:u32
tmp_r12:u32 = mem:?u32[(R0:u32 + low:u32(0xA0:u64)),e_little]:u32
R12:u32 = tmp_r12:u32
jmp  "pc_0xAF0"

addr 0xAF0 @asm  "add r3, r12, r3, lsl #2"
label pc_0xAF0
PC:u32 = 0xAF0:u32
tmp_r3:u32 = (R12:u32 + (R3:u32 << low:u32(0x2:u64)))
R3:u32 = tmp_r3:u32
jmp  "pc_0xAF4"

addr 0xAF4 @asm  "ldr r3, [r3, #76]"
label pc_0xAF4
PC:u32 = 0xAF4:u32
tmp_r3:u32 = mem:?u32[(R3:u32 + low:u32(0x4C:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0xAF8"

addr 0xAF8 @asm  "str r3, [r1, #8]"
label pc_0xAF8
PC:u32 = 0xAF8:u32
mem:?u32 = mem:?u32 with [(R1:u32 + low:u32(0x8:u64)) ,e_little]:u32 =R3:u32
jmp  "pc_0xAFC"

addr 0xAFC @asm  "mov r3, r2"
label pc_0xAFC
PC:u32 = 0xAFC:u32
tmp_r3:u32 = R2:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0xB00"

addr 0xB00 @asm  "cmp r3, #1"
label pc_0xB00
PC:u32 = 0xB00:u32
tmp_n_flag:bool = low:bool(low:bool(((R3:u32 + low:u32(0xFFFFFFFF:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R3:u32) + 0xFFFFFFFE:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R3:u32) + 0xFFFFFFFE:u64 + 0x1:u64) else ((extend:u64(R3:u32) + 0xFFFFFFFE:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R3:u32) + 0xFFFFFFFE:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R3:u32 + low:u32(0xFFFFFFFF:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R3:u32) >> 0x1f:u32 ) & ~(low:bool((R3:u32) >> 0x1f:u32 ) == ((((extend:u64(R3:u32) + 0xFFFFFFFE:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xB04"

addr 0xB04 @asm  "bls -#36"
label pc_0xB04
PC:u32 = 0xB04:u32
TmpV_102:bool = low:bool( ((~ C_FLAG) | Z_FLAG))
cjmp TmpV_102:bool , "pc_0xAE0" , "pc_0xB08"

addr 0xB08 @asm  "add r2, r0, #84"
label pc_0xB08
PC:u32 = 0xB08:u32
tmp_r2:u32 = (R0:u32 + low:u32(0x54:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0xB0C"

addr 0xB0C @asm  "str r2, [r0, #156]"
label pc_0xB0C
PC:u32 = 0xB0C:u32
mem:?u32 = mem:?u32 with [(R0:u32 + low:u32(0x9C:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0xB10"

addr 0xB10 @asm  "ldr r2, [r0, #160]"
label pc_0xB10
PC:u32 = 0xB10:u32
tmp_r2:u32 = mem:?u32[(R0:u32 + low:u32(0xA0:u64)),e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0xB14"

addr 0xB14 @asm  "ldmia r2, {r1, r2}"
label pc_0xB14
PC:u32 = 0xB14:u32
tmp_r2:u32 = mem:?u32[(R2:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r1:u32 = mem:?u32[R2:u32,e_little]:u32
R1:u32 = tmp_r1:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0xB18"

addr 0xB18 @asm  "mov r3, #1"
label pc_0xB18
PC:u32 = 0xB18:u32
tmp_r3:u32 = low:u32(0x1:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0xB1C"

addr 0xB1C @asm  "str r3, [r0, #4]"
label pc_0xB1C
PC:u32 = 0xB1C:u32
mem:?u32 = mem:?u32 with [(R0:u32 + low:u32(0x4:u64)) ,e_little]:u32 =R3:u32
jmp  "pc_0xB20"

addr 0xB20 @asm  "str r2, [r0, #136]"
label pc_0xB20
PC:u32 = 0xB20:u32
mem:?u32 = mem:?u32 with [(R0:u32 + low:u32(0x88:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0xB24"

addr 0xB24 @asm  "mov r3, #0"
label pc_0xB24
PC:u32 = 0xB24:u32
tmp_r3:u32 = low:u32(0x0:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0xB28"

addr 0xB28 @asm  "mov r2, #208"
label pc_0xB28
PC:u32 = 0xB28:u32
tmp_r2:u32 = low:u32(0xD0:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0xB2C"

addr 0xB2C @asm  "str r2, [r0, #148]"
label pc_0xB2C
PC:u32 = 0xB2C:u32
mem:?u32 = mem:?u32 with [(R0:u32 + low:u32(0x94:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0xB30"

addr 0xB30 @asm  "str r3, [r0, #8]"
label pc_0xB30
PC:u32 = 0xB30:u32
mem:?u32 = mem:?u32 with [(R0:u32 + low:u32(0x8:u64)) ,e_little]:u32 =R3:u32
jmp  "pc_0xB34"

addr 0xB34 @asm  "str r1, [r0, #144]"
label pc_0xB34
PC:u32 = 0xB34:u32
mem:?u32 = mem:?u32 with [(R0:u32 + low:u32(0x90:u64)) ,e_little]:u32 =R1:u32
jmp  "pc_0xB38"

addr 0xB38 @asm  "ldr r2, [pc, #24]"
label pc_0xB38
PC:u32 = 0xB38:u32
tmp_r2:u32 = mem:?u32[(PC:u32 + low:u32(0x20:u64)),e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0xB3C"

addr 0xB3C @asm  "ldr r0, [r0, #164]"
label pc_0xB3C
PC:u32 = 0xB3C:u32
tmp_r0:u32 = mem:?u32[(R0:u32 + low:u32(0xA4:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xB40"

addr 0xB40 @asm  "cmp r0, r2"
label pc_0xB40
PC:u32 = 0xB40:u32
tmp_n_flag:bool = low:bool(low:bool(((R0:u32 +  -R2:u32)) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64) else ((extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == R2:u32))
tmp_v_flag:bool = low:bool((low:bool((R0:u32) >> 0x1f:u32 ) == low:bool(( ~R2:u32) >> 0x1f:u32 )) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xB44"

addr 0xB44 @asm  "bne -#100"
label pc_0xB44
PC:u32 = 0xB44:u32
TmpV_103:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_103:bool , "pc_0xAE0" , "pc_0xB48"

addr 0xB48 @asm  "ldr r3, [pc, #20]"
label pc_0xB48
PC:u32 = 0xB48:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x1C:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0xB4C"

addr 0xB4C @asm  "str r0, [r3]"
label pc_0xB4C
PC:u32 = 0xB4C:u32
mem:?u32 = mem:?u32 with [R3:u32 ,e_little]:u32 =R0:u32
jmp  "pc_0xB50"

addr 0xB50 @asm  "add r0, r0, #84"
label pc_0xB50
PC:u32 = 0xB50:u32
tmp_r0:u32 = (R0:u32 + low:u32(0x54:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0xB54"

addr 0xB54 @asm  "b -#2308"
label pc_0xB54
PC:u32 = 0xB54:u32
jmp  "pc_0x250"

addr 0xB58 @asm  "andeq r8, r0, r4, lsr r1"
label pc_0xB58
PC:u32 = 0xB58:u32
TmpV_104:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_104:bool , "L_207" , "pc_0xB5C"
label L_207
tmp_r8:u32 = (R0:u32 & (R4:u32 >> low:u32(extend:u64(R1:u32))))
R8:u32 = tmp_r8:u32
jmp  "pc_0xB5C"

addr 0xB5C @asm  "andeq r8, r0, r4, asr #4"
label pc_0xB5C
PC:u32 = 0xB5C:u32
TmpV_105:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_105:bool , "L_209" , "pc_0xB60"
label L_209
tmp_r8:u32 = (R0:u32 & (R4:u32 $>> low:u32(0x4:u64)))
R8:u32 = tmp_r8:u32
jmp  "pc_0xB60"

addr 0xB60 @asm  "andeq r8, r0, r0, lsl #1"
label pc_0xB60
PC:u32 = 0xB60:u32
TmpV_106:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_106:bool , "L_211" , "pc_0xB64"
label L_211
tmp_r8:u32 = (R0:u32 & (R0:u32 << low:u32(0x1:u64)))
R8:u32 = tmp_r8:u32
jmp  "pc_0xB64"

addr 0xB64 @asm  "andeq r8, r0, r0, lsr r1"
label pc_0xB64
PC:u32 = 0xB64:u32
TmpV_107:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_107:bool , "L_213" , "pc_0xB68"
label L_213
tmp_r8:u32 = (R0:u32 & (R0:u32 >> low:u32(extend:u64(R1:u32))))
R8:u32 = tmp_r8:u32
jmp  "pc_0xB68"


addr 0xB68 @asm  "push {r3, lr}"
label pc_0xB68
PC:u32 = 0xB68:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF8:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xB6C"

addr 0xB6C @asm  "mov r0, #1"
label pc_0xB6C
PC:u32 = 0xB6C:u32
tmp_r0:u32 = low:u32(0x1:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0xB70"

addr 0xB70 @asm  "bl -#780"
label pc_0xB70
PC:u32 = 0xB70:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x864"

addr 0xB74 @asm  "ldr r3, [pc, #32]"
label pc_0xB74
PC:u32 = 0xB74:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x28:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0xB78"

addr 0xB78 @asm  "ldr r3, [r3]"
label pc_0xB78
PC:u32 = 0xB78:u32
tmp_r3:u32 = mem:?u32[R3:u32,e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0xB7C"

addr 0xB7C @asm  "ldr r3, [r3, #160]"
label pc_0xB7C
PC:u32 = 0xB7C:u32
tmp_r3:u32 = mem:?u32[(R3:u32 + low:u32(0xA0:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0xB80"

addr 0xB80 @asm  "add r2, r3, #4"
label pc_0xB80
PC:u32 = 0xB80:u32
tmp_r2:u32 = (R3:u32 + low:u32(0x4:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0xB84"

addr 0xB84 @asm  "ldmia r2, {sp}^"
label pc_0xB84
PC:u32 = 0xB84:u32
tmp_sp:u32 = mem:?u32[R2:u32,e_little]:u32
SP:u32 = tmp_sp:u32
jmp  "pc_0xB88"

addr 0xB88 @asm  "ldr r3, [r3]"
label pc_0xB88
PC:u32 = 0xB88:u32
tmp_r3:u32 = mem:?u32[R3:u32,e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0xB8C"

addr 0xB8C @asm  "mov lr, r3"
label pc_0xB8C
PC:u32 = 0xB8C:u32
tmp_lr_svc:u32 = R3:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xB90"

addr 0xB90 @asm  "msr spsr_fc, #16"
label pc_0xB90
PC:u32 = 0xB90:u32
SVC_N_FLAG:bool = false
SVC_C_FLAG:bool = false
SVC_Z_FLAG:bool = false
SVC_V_FLAG:bool = false
SVC_Q_FLAG:bool = false
jmp "pc_0xB94"

PC:u32 = 0xB90:u32
jmp "lift_error"
jmp "lift_error"
jmp "lift_error"
jmp "lift_error"
jmp "lift_error"
SVC_N_FLAG:bool = tmp_svc_n_flag:bool
SVC_C_FLAG:bool = tmp_svc_c_flag:bool
SVC_Z_FLAG:bool = tmp_svc_z_flag:bool
SVC_V_FLAG:bool = tmp_svc_v_flag:bool
SVC_Q_FLAG:bool = tmp_svc_q_flag:bool
jmp  "pc_0xB94"

addr 0xB94 @asm  "movs pc, lr"
label pc_0xB94
PC:u32 = 0xB94:u32
tmp_n_flag:bool = low:bool(SVC_N_FLAG:bool)
tmp_c_flag:bool = low:bool(SVC_C_FLAG:bool)
tmp_z_flag:bool = low:bool(SVC_Z_FLAG:bool)
tmp_v_flag:bool = low:bool(SVC_V_FLAG:bool)
tmp_q_flag:bool = low:bool(SVC_Q_FLAG:bool)
tmp_e_flag:bool = low:bool(SVC_E_FLAG:bool)
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
Q_FLAG:bool = tmp_q_flag:bool
E_FLAG:bool = tmp_e_flag:bool
jmp  ((low:u32(( if ~SVC_J_FLAG:bool & ~SVC_T_FLAG:bool then 0x4:u64 else 0x2:u64))*LR_SVC:u32)$/low:u32(( if ~SVC_J_FLAG:bool & ~SVC_T_FLAG:bool then 0x4:u64 else 0x2:u64)))

addr 0xB98 @asm  "pop {r3, pc}"
label pc_0xB98
PC:u32 = 0xB98:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x8:u64))
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp "lift_error"

addr 0xB9C @asm  "andeq r8, r0, r0, lsr r1"
label pc_0xB9C
PC:u32 = 0xB9C:u32
TmpV_108:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_108:bool , "L_215" , "pc_0xBA0"
label L_215
tmp_r8:u32 = (R0:u32 & (R0:u32 >> low:u32(extend:u64(R1:u32))))
R8:u32 = tmp_r8:u32
jmp  "pc_0xBA0"


addr 0xBA0 @asm  "push {r4, lr}"
label pc_0xBA0
PC:u32 = 0xBA0:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF8:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R4:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xBA4"

addr 0xBA4 @asm  "bl -#2288"
label pc_0xBA4
PC:u32 = 0xBA4:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x2B4"

addr 0xBA8 @asm  "bl -#2024"
label pc_0xBA8
PC:u32 = 0xBA8:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x3C0"

addr 0xBAC @asm  "bl -#564"
label pc_0xBAC
PC:u32 = 0xBAC:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x978"

addr 0xBB0 @asm  "bl -#332"
label pc_0xBB0
PC:u32 = 0xBB0:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xA64"

addr 0xBB4 @asm  "bl -#272"
label pc_0xBB4
PC:u32 = 0xBB4:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xAA4"

addr 0xBB8 @asm  "ldr r0, [pc, #8]"
label pc_0xBB8
PC:u32 = 0xBB8:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x10:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xBBC"

addr 0xBBC @asm  "bl +#672"
label pc_0xBBC
PC:u32 = 0xBBC:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32


addr 0xBC0 @asm  "pop {r4, lr}"
label pc_0xBC0
PC:u32 = 0xBC0:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x8:u64))
tmp_lr_svc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R4:u32 = tmp_r4:u32
SP_SVC:u32 = tmp_sp_svc:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xBC4"

addr 0xBC4 @asm  "b -#92"
label pc_0xBC4
PC:u32 = 0xBC4:u32
jmp  "pc_0xB68"

addr 0xBC8 @asm  "muleq r0, sp, r2"
label pc_0xBC8
PC:u32 = 0xBC8:u32
TmpV_109:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_109:bool , "L_217" , "pc_0xBCC"
label L_217
tmp_r0:u32 = (SP_SVC:u32*R2:u32)
R0:u32 = tmp_r0:u32
jmp  "pc_0xBCC"


addr 0xBCC @asm  "ldr r3, [pc, #64]"
label pc_0xBCC
PC:u32 = 0xBCC:u32
tmp_r3:u32 = mem:?u32[(PC:u32 + low:u32(0x48:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0xBD0"

addr 0xBD0 @asm  "mov r0, r0, lsr #12"
label pc_0xBD0
PC:u32 = 0xBD0:u32
tmp_r0:u32 = (R0:u32 >> low:u32(0xC:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0xBD4"

addr 0xBD4 @asm  "cmp r3, #0"
label pc_0xBD4
PC:u32 = 0xBD4:u32
tmp_n_flag:bool = low:bool(low:bool((R3:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R3:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R3:u32) >> 0x1f:u32 ) & ~(low:bool((R3:u32) >> 0x1f:u32 ) == ((((extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xBD8"

addr 0xBD8 @asm  "beq +#52"
label pc_0xBD8
PC:u32 = 0xBD8:u32
TmpV_110:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_110:bool , "pc_0xC0C" , "pc_0xBDC"

addr 0xBDC @asm  "ldr r2, [r3]"
label pc_0xBDC
PC:u32 = 0xBDC:u32
tmp_r2:u32 = mem:?u32[R3:u32,e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0xBE0"

addr 0xBE0 @asm  "cmp r0, r2"
label pc_0xBE0
PC:u32 = 0xBE0:u32
tmp_n_flag:bool = low:bool(low:bool(((R0:u32 +  -R2:u32)) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64) else ((extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == R2:u32))
tmp_v_flag:bool = low:bool((low:bool((R0:u32) >> 0x1f:u32 ) == low:bool(( ~R2:u32) >> 0x1f:u32 )) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xBE4"

addr 0xBE4 @asm  "bcc +#20"
label pc_0xBE4
PC:u32 = 0xBE4:u32
TmpV_111:bool = low:bool( ~C_FLAG:bool)
cjmp TmpV_111:bool , "pc_0xBF8" , "pc_0xBE8"

addr 0xBE8 @asm  "ldr r1, [r3, #4]"
label pc_0xBE8
PC:u32 = 0xBE8:u32
tmp_r1:u32 = mem:?u32[(R3:u32 + low:u32(0x4:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0xBEC"

addr 0xBEC @asm  "add r2, r2, r1"
label pc_0xBEC
PC:u32 = 0xBEC:u32
tmp_r2:u32 = (R2:u32 + R1:u32)
R2:u32 = tmp_r2:u32
jmp  "pc_0xBF0"

addr 0xBF0 @asm  "cmp r0, r2"
label pc_0xBF0
PC:u32 = 0xBF0:u32
tmp_n_flag:bool = low:bool(low:bool(((R0:u32 +  -R2:u32)) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64) else ((extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == R2:u32))
tmp_v_flag:bool = low:bool((low:bool((R0:u32) >> 0x1f:u32 ) == low:bool(( ~R2:u32) >> 0x1f:u32 )) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + extend:u64( ~R2:u32) + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xBF4"

addr 0xBF4 @asm  "bls +#24"
label pc_0xBF4
PC:u32 = 0xBF4:u32
jmp "lift_error"
cjmp TmpV_112:bool , "pc_0xC0C" , "pc_0xBF8"

addr 0xBF8 @asm  "ldr r2, [r3, #12]"
label pc_0xBF8
PC:u32 = 0xBF8:u32
tmp_r2:u32 = mem:?u32[(R3:u32 + low:u32(0xC:u64)),e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0xBFC"

addr 0xBFC @asm  "tst r2, #1"
label pc_0xBFC
PC:u32 = 0xBFC:u32
tmp_n_flag:bool = low:bool(low:bool(((R2:u32 & low:u32(0x1:u64))) >> 0x1f:u32 ))
tmp_z_flag:bool = low:bool(((R2:u32 & low:u32(0x1:u64)) == low:u32(0x0:u64)))
N_FLAG:bool = tmp_n_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
jmp  "pc_0xC00"

addr 0xC00 @asm  "addeq r3, r3, #16"
label pc_0xC00
PC:u32 = 0xC00:u32
TmpV_113:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_113:bool , "L_225" , "pc_0xC04"
label L_225
tmp_r3:u32 = (R3:u32 + low:u32(0x10:u64))
R3:u32 = tmp_r3:u32
jmp  "pc_0xC04"

addr 0xC04 @asm  "beq -#48"
label pc_0xC04
PC:u32 = 0xC04:u32
TmpV_114:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_114:bool , "pc_0xBD4" , "pc_0xC08"

addr 0xC08 @asm  "mov r3, #0"
label pc_0xC08
PC:u32 = 0xC08:u32
tmp_r3:u32 = low:u32(0x0:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0xC0C"

addr 0xC0C @asm  "mov r0, r3"
label pc_0xC0C
PC:u32 = 0xC0C:u32
tmp_r0:u32 = R3:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xC10"

addr 0xC10 @asm  "mov pc, lr"
label pc_0xC10
PC:u32 = 0xC10:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0xC14 @asm  "andeq r8, r0, r4, ror #3"
label pc_0xC14
PC:u32 = 0xC14:u32
TmpV_115:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_115:bool , "L_229" , "pc_0xC18"
label L_229
jmp "lift_error"
R8:u32 = tmp_r8:u32
jmp  "pc_0xC18"


addr 0xC18 @asm  "b -#1584"
label pc_0xC18
PC:u32 = 0xC18:u32
jmp  "pc_0x5E8"


addr 0xC1C @asm  "cmp r0, #1"
label pc_0xC1C
PC:u32 = 0xC1C:u32
tmp_n_flag:bool = low:bool(low:bool(((R0:u32 + low:u32(0xFFFFFFFF:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R0:u32 + low:u32(0xFFFFFFFF:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFE:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xC20"

addr 0xC20 @asm  "push {r3, lr}"
label pc_0xC20
PC:u32 = 0xC20:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF8:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xC24"

addr 0xC24 @asm  "mov r1, r0"
label pc_0xC24
PC:u32 = 0xC24:u32
tmp_r1:u32 = R0:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0xC28"

addr 0xC28 @asm  "bne +#16"
label pc_0xC28
PC:u32 = 0xC28:u32
TmpV_116:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_116:bool , "pc_0xC38" , "pc_0xC2C"

addr 0xC2C @asm  "ldr r0, [pc, #16]"
label pc_0xC2C
PC:u32 = 0xC2C:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x18:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xC30"

addr 0xC30 @asm  "bl +#556"
label pc_0xC30
PC:u32 = 0xC30:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32


addr 0xC34 @asm  "b +#12"
label pc_0xC34
PC:u32 = 0xC34:u32
jmp  "pc_0xC40"

addr 0xC38 @asm  "ldr r0, [pc, #8]"
label pc_0xC38
PC:u32 = 0xC38:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x10:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xC3C"

addr 0xC3C @asm  "bl +#544"
label pc_0xC3C
PC:u32 = 0xC3C:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32


addr 0xC40 @asm  "b +#0"
label pc_0xC40
PC:u32 = 0xC40:u32
jmp  "pc_0xC40"

addr 0xC44 @asm  "andeq r1, r0, r1, lsl r3"
label pc_0xC44
PC:u32 = 0xC44:u32
TmpV_117:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_117:bool , "L_233" , "pc_0xC48"
label L_233
tmp_r1:u32 = (R0:u32 & (R1:u32 << low:u32(extend:u64(R3:u32))))
R1:u32 = tmp_r1:u32
jmp  "pc_0xC48"

addr 0xC48 @asm  "andeq r1, r0, pc, lsr r3"
label pc_0xC48

jmp "lift_error"


addr 0xC4C @asm  "msr cpsr_c, #211"
label pc_0xC4C
PC:u32 = 0xC4C:u32
jmp  "pc_0xC50"

addr 0xC50 @asm  "mov r0, #0"
label pc_0xC50
PC:u32 = 0xC50:u32
tmp_r0:u32 = low:u32(0x0:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0xC54"

addr 0xC54 @asm  "ldr r1, [pc, #96]"
label pc_0xC54
PC:u32 = 0xC54:u32
tmp_r1:u32 = mem:?u32[(PC:u32 + low:u32(0x68:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0xC58"

addr 0xC58 @asm  "ldr r2, [pc, #96]"
label pc_0xC58
PC:u32 = 0xC58:u32
tmp_r2:u32 = mem:?u32[(PC:u32 + low:u32(0x68:u64)),e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0xC5C"


addr 0xC5C @asm  "str r0, [r1], #4"
label pc_0xC5C
PC:u32 = 0xC5C:u32
tmp_r1:u32 = (R1:u32 + low:u32(0x4:u64))
mem:?u32 = mem:?u32 with [R1:u32 ,e_little]:u32 =R0:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0xC60"

addr 0xC60 @asm  "cmp r1, r2"
label pc_0xC60
PC:u32 = 0xC60:u32
tmp_n_flag:bool = low:bool(low:bool(((R1:u32 +  -R2:u32)) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + extend:u64( ~R2:u32) + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + extend:u64( ~R2:u32) + 0x1:u64) else ((extend:u64(R1:u32) + extend:u64( ~R2:u32) + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + extend:u64( ~R2:u32) + 0x1:u64)))
tmp_z_flag:bool = low:bool((R1:u32 == R2:u32))
tmp_v_flag:bool = low:bool((low:bool((R1:u32) >> 0x1f:u32 ) == low:bool(( ~R2:u32) >> 0x1f:u32 )) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + extend:u64( ~R2:u32) + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xC64"

addr 0xC64 @asm  "bcc -#8"
label pc_0xC64
PC:u32 = 0xC64:u32
TmpV_118:bool = low:bool( ~C_FLAG:bool)
cjmp TmpV_118:bool , "pc_0xC5C" , "pc_0xC68"

addr 0xC68 @asm  "ldr r0, [pc, #84]"
label pc_0xC68
PC:u32 = 0xC68:u32
tmp_r0:u32 = mem:?u32[(PC:u32 + low:u32(0x5C:u64)),e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xC6C"

addr 0xC6C @asm  "msr cpsr_c, #210"
label pc_0xC6C
PC:u32 = 0xC6C:u32
jmp  "pc_0xC70"

addr 0xC70 @asm  "mov sp, r0"
label pc_0xC70
PC:u32 = 0xC70:u32
tmp_sp_svc:u32 = R0:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xC74"

addr 0xC74 @asm  "sub r0, r0, #4096"
label pc_0xC74
PC:u32 = 0xC74:u32
tmp_r0:u32 = (R0:u32 + low:u32(0xFFFFF000:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0xC78"

addr 0xC78 @asm  "msr cpsr_c, #209"
label pc_0xC78
PC:u32 = 0xC78:u32
jmp  "pc_0xC7C"

addr 0xC7C @asm  "mov sp, r0"
label pc_0xC7C
PC:u32 = 0xC7C:u32
tmp_sp_svc:u32 = R0:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xC80"

addr 0xC80 @asm  "sub r0, r0, #4096"
label pc_0xC80
PC:u32 = 0xC80:u32
tmp_r0:u32 = (R0:u32 + low:u32(0xFFFFF000:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0xC84"

addr 0xC84 @asm  "msr cpsr_c, #215"
label pc_0xC84
PC:u32 = 0xC84:u32
jmp  "pc_0xC88"

addr 0xC88 @asm  "mov sp, r0"
label pc_0xC88
PC:u32 = 0xC88:u32
tmp_sp_svc:u32 = R0:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xC8C"

addr 0xC8C @asm  "sub r0, r0, #4096"
label pc_0xC8C
PC:u32 = 0xC8C:u32
tmp_r0:u32 = (R0:u32 + low:u32(0xFFFFF000:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0xC90"

addr 0xC90 @asm  "msr cpsr_c, #219"
label pc_0xC90
PC:u32 = 0xC90:u32
jmp  "pc_0xC94"

addr 0xC94 @asm  "mov sp, r0"
label pc_0xC94
PC:u32 = 0xC94:u32
tmp_sp_svc:u32 = R0:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xC98"

addr 0xC98 @asm  "sub r0, r0, #4096"
label pc_0xC98
PC:u32 = 0xC98:u32
tmp_r0:u32 = (R0:u32 + low:u32(0xFFFFF000:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0xC9C"

addr 0xC9C @asm  "msr cpsr_c, #223"
label pc_0xC9C
PC:u32 = 0xC9C:u32
jmp  "pc_0xCA0"

addr 0xCA0 @asm  "mov sp, r0"
label pc_0xCA0
PC:u32 = 0xCA0:u32
tmp_sp_svc:u32 = R0:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xCA4"

addr 0xCA4 @asm  "sub r0, r0, #4096"
label pc_0xCA4
PC:u32 = 0xCA4:u32
tmp_r0:u32 = (R0:u32 + low:u32(0xFFFFF000:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0xCA8"

addr 0xCA8 @asm  "msr cpsr_c, #211"
label pc_0xCA8
PC:u32 = 0xCA8:u32
jmp  "pc_0xCAC"

addr 0xCAC @asm  "mov sp, r0"
label pc_0xCAC
PC:u32 = 0xCAC:u32
tmp_sp_svc:u32 = R0:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xCB0"

addr 0xCB0 @asm  "sub r0, r0, #4096"
label pc_0xCB0
PC:u32 = 0xCB0:u32
tmp_r0:u32 = (R0:u32 + low:u32(0xFFFFF000:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0xCB4"

addr 0xCB4 @asm  "bl -#276"
label pc_0xCB4
PC:u32 = 0xCB4:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xBA0"


addr 0xCB8 @asm  "bl +#0"
label pc_0xCB8
PC:u32 = 0xCB8:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xCB8"

addr 0xCBC @asm  "andeq r2, r0, r0"
label pc_0xCBC
PC:u32 = 0xCBC:u32
TmpV_119:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_119:bool , "L_237" , "pc_0xCC0"
label L_237
tmp_r2:u32 = R0:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0xCC0"

addr 0xCC0 @asm  "andeq r8, r0, r0"
label pc_0xCC0
PC:u32 = 0xCC0:u32
TmpV_120:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_120:bool , "L_239" , "pc_0xCC4"
label L_239
tmp_r8:u32 = R0:u32
R8:u32 = tmp_r8:u32
jmp  "pc_0xCC4"

addr 0xCC4 @asm  "strdeq pc, r0, [pc], -r12"
label pc_0xCC4

jmp "lift_error"


addr 0xCC8 @asm  "mcr p15, #0, r0, c3, c0"
label pc_0xCC8
PC:u32 = 0xCC8:u32
CR3:u32 = R0:u32
CR0:u32 = 0:u32
jmp "pc_0xCCC"


jmp "lift_error"

addr 0xCCC @asm  "bx lr"
label pc_0xCCC
PC:u32 = 0xCCC:u32
cjmp (LR_SVC<>0x7E8:u32), "lift_error", "pc_0x7E8"

jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0xCD0 @asm  "mcr p15, #0, r0, c2, c0"
label pc_0xCD0
PC:u32 = 0xCD0:u32
CR2:u32 = R0:u32
CR0:u32 = 0:u32
jmp "pc_0xCD4"


jmp "lift_error"

addr 0xCD4 @asm  "bx lr"
label pc_0xCD4
PC:u32 = 0xCD4:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0xCD8 @asm  "mrc p15, #0, r1, c1, c0"
label pc_0xCD8
PC:u32 = 0xCD8:u32
R1:u32 = CR1:u32
jmp "pc_0xCDC"


jmp "lift_error"

addr 0xCDC @asm  "cmp r0, #0"
label pc_0xCDC
PC:u32 = 0xCDC:u32
tmp_n_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xCE0"

addr 0xCE0 @asm  "orrne r1, r1, #1"
label pc_0xCE0
PC:u32 = 0xCE0:u32
TmpV_121:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_121:bool , "L_241" , "pc_0xCE4"
label L_241
tmp_r1:u32 = R1:u32 | low:u32(0x1:u64)
R1:u32 = tmp_r1:u32
jmp  "pc_0xCE4"

addr 0xCE4 @asm  "biceq r1, r1, #1"
label pc_0xCE4
PC:u32 = 0xCE4:u32
TmpV_122:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_122:bool , "L_243" , "pc_0xCE8"
label L_243
tmp_r1:u32 = (R1:u32 & low:u32(0xFFFFFFFE:u64))
R1:u32 = tmp_r1:u32
jmp  "pc_0xCE8"

addr 0xCE8 @asm  "mcr p15, #0, r1, c1, c0"
label pc_0xCE8
PC:u32 = 0xCE8:u32
CR1:u32 = R0:u32
CR0:u32 = 0:u32
jmp "pc_0xCEC"


jmp "lift_error"

addr 0xCEC @asm  "bx lr"
label pc_0xCEC
PC:u32 = 0xCEC:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0xCF0 @asm  "mov r0, r0, lsl #25"
label pc_0xCF0
PC:u32 = 0xCF0:u32
tmp_r0:u32 = (R0:u32 << low:u32(0x19:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0xCF4"

addr 0xCF4 @asm  "mcr p15, #0, r0, c13, c0"
label pc_0xCF4

jmp "lift_error"

addr 0xCF8 @asm  "bx lr"
label pc_0xCF8
PC:u32 = 0xCF8:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0xCFC @asm  "mrc p15, #0, r0, c13, c0"
label pc_0xCFC

jmp "lift_error"

addr 0xD00 @asm  "mov r0, r0, lsr #25"
label pc_0xD00
PC:u32 = 0xD00:u32
tmp_r0:u32 = (R0:u32 >> low:u32(0x19:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0xD04"

addr 0xD04 @asm  "bx lr"
label pc_0xD04
PC:u32 = 0xD04:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0xD08 @asm  "mrs r1, cpsr"
label pc_0xD08
PC:u32 = 0xD08:u32
jmp "lift_error"
R1:u32 = tmp_r1:u32
jmp  "pc_0xD0C"

addr 0xD0C @asm  "and r2, r1, #192"
label pc_0xD0C
PC:u32 = 0xD0C:u32
tmp_r2:u32 = (R1:u32 & low:u32(0xC0:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0xD10"

addr 0xD10 @asm  "bic r1, r1, #192"
label pc_0xD10
PC:u32 = 0xD10:u32
tmp_r1:u32 = (R1:u32 & low:u32(0xFFFFFF3F:u64))
R1:u32 = tmp_r1:u32
jmp  "pc_0xD14"

addr 0xD14 @asm  "orr r1, r1, r0"
label pc_0xD14
PC:u32 = 0xD14:u32
tmp_r1:u32 = R1:u32 | R0:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0xD18"

addr 0xD18 @asm  "mov r0, r1"
label pc_0xD18
PC:u32 = 0xD18:u32
tmp_r0:u32 = R1:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xD1C"

addr 0xD1C @asm  "msr cpsr_c, r1"
label pc_0xD1C
PC:u32 = 0xD1C:u32
jmp  "pc_0xD20"

addr 0xD20 @asm  "bx lr"
label pc_0xD20
PC:u32 = 0xD20:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0xD24 @asm  "mrs r1, spsr"
label pc_0xD24
PC:u32 = 0xD24:u32
tmp_r1:u32 = (((extend:u32(SVC_N_FLAG:bool) << 31:u32)& (0x1:u32 << 31:u32))|((extend:u32(SVC_Z_FLAG:bool) << 30:u32)& (0x1:u32 << 30:u32))|((extend:u32(SVC_C_FLAG:bool) << 29:u32)& (0x1:u32 << 29:u32))|((extend:u32(SVC_V_FLAG:bool) << 28:u32)& (0x1:u32 << 28:u32))|((extend:u32(SVC_Q_FLAG:bool) << 27:u32)& (0x1:u32 << 27:u32))|((extend:u32(SVC_J_FLAG:bool) << 24:u32)& (0x1:u32 << 24:u32))|((extend:u32(SVC_E_FLAG:bool) << 9:u32)& (0x1:u32 << 9:u32))|((extend:u32(SVC_A_FLAG:bool) << 8:u32)& (0x1:u32 << 8:u32))|((extend:u32(SVC_I_FLAG:bool) << 7:u32)& (0x1:u32 << 7:u32))|((extend:u32(SVC_F_FLAG:bool) << 6:u32)& (0x1:u32 << 6:u32))|((extend:u32(SVC_T_FLAG:bool) << 5:u32)& (0x1:u32 << 5:u32)))
R1:u32 = tmp_r1:u32
jmp  "pc_0xD28"

addr 0xD28 @asm  "and r2, r1, #192"
label pc_0xD28
PC:u32 = 0xD28:u32
tmp_r2:u32 = (R1:u32 & low:u32(0xC0:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0xD2C"

addr 0xD2C @asm  "bic r1, r1, #192"
label pc_0xD2C
PC:u32 = 0xD2C:u32
tmp_r1:u32 = (R1:u32 & low:u32(0xFFFFFF3F:u64))
R1:u32 = tmp_r1:u32
jmp  "pc_0xD30"

addr 0xD30 @asm  "orr r1, r1, r0"
label pc_0xD30
PC:u32 = 0xD30:u32
tmp_r1:u32 = R1:u32 | R0:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0xD34"

addr 0xD34 @asm  "mov r0, r1"
label pc_0xD34
PC:u32 = 0xD34:u32
tmp_r0:u32 = R1:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xD38"

addr 0xD38 @asm  "msr spsr_c, r1"
label pc_0xD38
PC:u32 = 0xD38:u32
jmp  "pc_0xD3C"

addr 0xD3C @asm  "bx lr"
label pc_0xD3C
PC:u32 = 0xD3C:u32
cjmp (LR_SVC<>0x7CC:u32), "lift_error", "pc_0x7CC"

jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0xD40 @asm  "push {r4, lr}"
label pc_0xD40
PC:u32 = 0xD40:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF8:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R4:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xD44"

addr 0xD44 @asm  "mov r4, r0"
label pc_0xD44
PC:u32 = 0xD44:u32
tmp_r4:u32 = R0:u32
R4:u32 = tmp_r4:u32
jmp  "pc_0xD48"

addr 0xD48 @asm  "b +#8"
label pc_0xD48
PC:u32 = 0xD48:u32
jmp  "pc_0xD50"

addr 0xD4C @asm  "bl -#308"
label pc_0xD4C
PC:u32 = 0xD4C:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xC18"

addr 0xD50 @asm  "ldrb r0, [r4], #1"
label pc_0xD50
PC:u32 = 0xD50:u32
tmp_r4:u32 = (R4:u32 + low:u32(0x1:u64))
r0:u32 = pad:u32(mem:?u32[R4:u32 ,e_little]:u8)
R0:u32 = tmp_r0:u32
R4:u32 = tmp_r4:u32
jmp  "pc_0xD54"

addr 0xD54 @asm  "cmp r0, #0"
label pc_0xD54
PC:u32 = 0xD54:u32
tmp_n_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xD58"

addr 0xD58 @asm  "bne -#12"
label pc_0xD58
PC:u32 = 0xD58:u32
TmpV_123:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_123:bool , "pc_0xD4C" , "pc_0xD5C"

addr 0xD5C @asm  "pop {r4, lr}"
label pc_0xD5C
PC:u32 = 0xD5C:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x8:u64))
tmp_lr_svc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R4:u32 = tmp_r4:u32
SP_SVC:u32 = tmp_sp_svc:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xD60"

addr 0xD60 @asm  "bx lr"
label pc_0xD60
PC:u32 = 0xD60:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0xD64 @asm  "push {r0-r6, lr}"
label pc_0xD64
PC:u32 = 0xD64:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFE0:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R6:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF4:u64)) ,e_little]:u32 =R5:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF0:u64)) ,e_little]:u32 =R4:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFEC:u64)) ,e_little]:u32 =R3:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFE8:u64)) ,e_little]:u32 =R2:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFE4:u64)) ,e_little]:u32 =R1:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFE0:u64)) ,e_little]:u32 =R0:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xD68"

addr 0xD68 @asm  "subs r5, r0, #0"
label pc_0xD68
PC:u32 = 0xD68:u32
tmp_r5:u32 = R0:u32
tmp_n_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
R5:u32 = tmp_r5:u32
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xD6C"

addr 0xD6C @asm  "rsblt r5, r5, #0"
label pc_0xD6C
PC:u32 = 0xD6C:u32
TmpV_124:bool = low:bool( ~(N_FLAG:bool == V_FLAG:bool))
cjmp TmpV_124:bool , "L_247" , "pc_0xD70"
label L_247
tmp_r5:u32 =  -R5:u32
R5:u32 = tmp_r5:u32
jmp  "pc_0xD70"

addr 0xD70 @asm  "movlt r6, #1"
label pc_0xD70
PC:u32 = 0xD70:u32
TmpV_125:bool = low:bool( ~(N_FLAG:bool == V_FLAG:bool))
cjmp TmpV_125:bool , "L_249" , "pc_0xD74"
label L_249
tmp_r6:u32 = low:u32(0x1:u64)
R6:u32 = tmp_r6:u32
jmp  "pc_0xD74"

addr 0xD74 @asm  "movge r6, #0"
label pc_0xD74
PC:u32 = 0xD74:u32
TmpV_126:bool = low:bool( (N_FLAG:bool == V_FLAG:bool))
cjmp TmpV_126:bool , "L_251" , "pc_0xD78"
label L_251
tmp_r6:u32 = low:u32(0x0:u64)
R6:u32 = tmp_r6:u32
jmp  "pc_0xD78"

addr 0xD78 @asm  "mov r4, #0"
label pc_0xD78
PC:u32 = 0xD78:u32
tmp_r4:u32 = low:u32(0x0:u64)
R4:u32 = tmp_r4:u32
jmp  "pc_0xD7C"

addr 0xD7C @asm  "mov r0, r5"
label pc_0xD7C
PC:u32 = 0xD7C:u32
tmp_r0:u32 = R5:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xD80"

addr 0xD80 @asm  "mov r1, #10"
label pc_0xD80
PC:u32 = 0xD80:u32
tmp_r1:u32 = low:u32(0xA:u64)
R1:u32 = tmp_r1:u32
jmp  "pc_0xD84"

addr 0xD84 @asm  "bl +#792"
label pc_0xD84
PC:u32 = 0xD84:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x109C"

addr 0xD88 @asm  "add r3, sp, #4"
label pc_0xD88
PC:u32 = 0xD88:u32
tmp_r3:u32 = (SP_SVC:u32 + low:u32(0x4:u64))
R3:u32 = tmp_r3:u32
jmp  "pc_0xD8C"

addr 0xD8C @asm  "add r1, r1, #48"
label pc_0xD8C
PC:u32 = 0xD8C:u32
tmp_r1:u32 = (R1:u32 + low:u32(0x30:u64))
R1:u32 = tmp_r1:u32
jmp  "pc_0xD90"

addr 0xD90 @asm  "strb r1, [r3, r4]"
label pc_0xD90
PC:u32 = 0xD90:u32
mem:?u32 = mem:?u32 with [(R3:u32 + R4:u32) ,e_little]:u8 = (low:u8(R1:u32))jmp  "pc_0xD94"

addr 0xD94 @asm  "mov r0, r5"
label pc_0xD94
PC:u32 = 0xD94:u32
tmp_r0:u32 = R5:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xD98"

addr 0xD98 @asm  "mov r1, #10"
label pc_0xD98
PC:u32 = 0xD98:u32
tmp_r1:u32 = low:u32(0xA:u64)
R1:u32 = tmp_r1:u32
jmp  "pc_0xD9C"

addr 0xD9C @asm  "bl +#472"
label pc_0xD9C
PC:u32 = 0xD9C:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xF74"

addr 0xDA0 @asm  "subs r5, r0, #0"
label pc_0xDA0
PC:u32 = 0xDA0:u32
tmp_r5:u32 = R0:u32
tmp_n_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
R5:u32 = tmp_r5:u32
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xDA4"

addr 0xDA4 @asm  "add r4, r4, #1"
label pc_0xDA4
PC:u32 = 0xDA4:u32
tmp_r4:u32 = (R4:u32 + low:u32(0x1:u64))
R4:u32 = tmp_r4:u32
jmp  "pc_0xDA8"

addr 0xDA8 @asm  "bne -#44"
label pc_0xDA8
PC:u32 = 0xDA8:u32
TmpV_127:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_127:bool , "pc_0xD7C" , "pc_0xDAC"

addr 0xDAC @asm  "cmp r6, #0"
label pc_0xDAC
PC:u32 = 0xDAC:u32
tmp_n_flag:bool = low:bool(low:bool((R6:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R6:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R6:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R6:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R6:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R6:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R6:u32) >> 0x1f:u32 ) & ~(low:bool((R6:u32) >> 0x1f:u32 ) == ((((extend:u64(R6:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xDB0"

addr 0xDB0 @asm  "addne r2, sp, #16"
label pc_0xDB0
PC:u32 = 0xDB0:u32
TmpV_128:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_128:bool , "L_255" , "pc_0xDB4"
label L_255
tmp_r2:u32 = (SP_SVC:u32 + low:u32(0x10:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0xDB4"

addr 0xDB4 @asm  "addne r3, r2, r4"
label pc_0xDB4
PC:u32 = 0xDB4:u32
TmpV_129:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_129:bool , "L_257" , "pc_0xDB8"
label L_257
tmp_r3:u32 = (R2:u32 + R4:u32)
R3:u32 = tmp_r3:u32
jmp  "pc_0xDB8"

addr 0xDB8 @asm  "movne r2, #45"
label pc_0xDB8
PC:u32 = 0xDB8:u32
TmpV_130:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_130:bool , "L_259" , "pc_0xDBC"
label L_259
tmp_r2:u32 = low:u32(0x2D:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0xDBC"

addr 0xDBC @asm  "strbne r2, [r3, #-12]"
label pc_0xDBC
PC:u32 = 0xDBC:u32
TmpV_131:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_131:bool , "L_261" , "pc_0xDC0"
label L_261
mem:?u32 = mem:?u32 with [(R3:u32 + low:u32(0xFFFFFFF4:u64)) ,e_little]:u8 = (low:u8(R2:u32))jmp  "pc_0xDC0"

addr 0xDC0 @asm  "addne r4, r4, #1"
label pc_0xDC0
PC:u32 = 0xDC0:u32
TmpV_132:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_132:bool , "L_263" , "pc_0xDC4"
label L_263
tmp_r4:u32 = (R4:u32 + low:u32(0x1:u64))
R4:u32 = tmp_r4:u32
jmp  "pc_0xDC4"

addr 0xDC4 @asm  "sub r4, r4, #1"
label pc_0xDC4
PC:u32 = 0xDC4:u32
tmp_r4:u32 = (R4:u32 + low:u32(0xFFFFFFFF:u64))
R4:u32 = tmp_r4:u32
jmp  "pc_0xDC8"

addr 0xDC8 @asm  "add r3, sp, #4"
label pc_0xDC8
PC:u32 = 0xDC8:u32
tmp_r3:u32 = (SP_SVC:u32 + low:u32(0x4:u64))
R3:u32 = tmp_r3:u32
jmp  "pc_0xDCC"

addr 0xDCC @asm  "ldrb r0, [r3, r4]"
label pc_0xDCC
PC:u32 = 0xDCC:u32
r0:u32 = pad:u32(mem:?u32[(R3:u32 + R4:u32) ,e_little]:u8)
R0:u32 = tmp_r0:u32
jmp  "pc_0xDD0"

addr 0xDD0 @asm  "bl -#440"
label pc_0xDD0
PC:u32 = 0xDD0:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xC18"

addr 0xDD4 @asm  "cmp r4, #0"
label pc_0xDD4
PC:u32 = 0xDD4:u32
tmp_n_flag:bool = low:bool(low:bool((R4:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R4:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R4:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R4:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R4:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R4:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R4:u32) >> 0x1f:u32 ) & ~(low:bool((R4:u32) >> 0x1f:u32 ) == ((((extend:u64(R4:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xDD8"

addr 0xDD8 @asm  "bne -#20"
label pc_0xDD8
PC:u32 = 0xDD8:u32
TmpV_133:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_133:bool , "pc_0xDC4" , "pc_0xDDC"

addr 0xDDC @asm  "pop {r0-r6, lr}"
label pc_0xDDC
PC:u32 = 0xDDC:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x20:u64))
tmp_lr_svc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x1C:u64)),e_little]:u32
tmp_r6:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x18:u64)),e_little]:u32
tmp_r5:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x14:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x10:u64)),e_little]:u32
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r2:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r1:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r0:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R0:u32 = tmp_r0:u32
R1:u32 = tmp_r1:u32
R2:u32 = tmp_r2:u32
R3:u32 = tmp_r3:u32
R4:u32 = tmp_r4:u32
R5:u32 = tmp_r5:u32
R6:u32 = tmp_r6:u32
SP_SVC:u32 = tmp_sp_svc:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xDE0"

addr 0xDE0 @asm  "bx lr"
label pc_0xDE0
PC:u32 = 0xDE0:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0xDE4 @asm  "push {r3-r5, lr}"
label pc_0xDE4
PC:u32 = 0xDE4:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF0:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R5:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF4:u64)) ,e_little]:u32 =R4:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF0:u64)) ,e_little]:u32 =R3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xDE8"

addr 0xDE8 @asm  "mov r5, r0"
label pc_0xDE8
PC:u32 = 0xDE8:u32
tmp_r5:u32 = R0:u32
R5:u32 = tmp_r5:u32
jmp  "pc_0xDEC"

addr 0xDEC @asm  "mov r4, #7"
label pc_0xDEC
PC:u32 = 0xDEC:u32
tmp_r4:u32 = low:u32(0x7:u64)
R4:u32 = tmp_r4:u32
jmp  "pc_0xDF0"

addr 0xDF0 @asm  "mov r0, r5, lsr #28"
label pc_0xDF0
PC:u32 = 0xDF0:u32
tmp_r0:u32 = (R5:u32 >> low:u32(0x1C:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0xDF4"

addr 0xDF4 @asm  "cmp r0, #9"
label pc_0xDF4
PC:u32 = 0xDF4:u32
tmp_n_flag:bool = low:bool(low:bool(((R0:u32 + low:u32(0xFFFFFFF7:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFF6:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFF6:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFF6:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFF6:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R0:u32 + low:u32(0xFFFFFFF7:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFF6:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xDF8"

addr 0xDF8 @asm  "addle r0, r0, #48"
label pc_0xDF8
PC:u32 = 0xDF8:u32
jmp "lift_error"
cjmp TmpV_134:bool , "L_267" , "pc_0xDFC"
label L_267
tmp_r0:u32 = (R0:u32 + low:u32(0x30:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0xDFC"

addr 0xDFC @asm  "addgt r0, r0, #55"
label pc_0xDFC
PC:u32 = 0xDFC:u32
TmpV_135:bool = low:bool( (N_FLAG:bool == V_FLAG:bool) & ~Z_FLAG:bool)
cjmp TmpV_135:bool , "L_269" , "pc_0xE00"
label L_269
tmp_r0:u32 = (R0:u32 + low:u32(0x37:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0xE00"

addr 0xE00 @asm  "bl -#488"
label pc_0xE00
PC:u32 = 0xE00:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xC18"

addr 0xE04 @asm  "cmp r4, #0"
label pc_0xE04
PC:u32 = 0xE04:u32
tmp_n_flag:bool = low:bool(low:bool((R4:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R4:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R4:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R4:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R4:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R4:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R4:u32) >> 0x1f:u32 ) & ~(low:bool((R4:u32) >> 0x1f:u32 ) == ((((extend:u64(R4:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xE08"

addr 0xE08 @asm  "mov r5, r5, lsl #4"
label pc_0xE08
PC:u32 = 0xE08:u32
tmp_r5:u32 = (R5:u32 << low:u32(0x4:u64))
R5:u32 = tmp_r5:u32
jmp  "pc_0xE0C"

addr 0xE0C @asm  "subne r4, r4, #1"
label pc_0xE0C
PC:u32 = 0xE0C:u32
TmpV_136:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_136:bool , "L_271" , "pc_0xE10"
label L_271
tmp_r4:u32 = (R4:u32 + low:u32(0xFFFFFFFF:u64))
R4:u32 = tmp_r4:u32
jmp  "pc_0xE10"

addr 0xE10 @asm  "bne -#32"
label pc_0xE10
PC:u32 = 0xE10:u32
TmpV_137:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_137:bool , "pc_0xDF0" , "pc_0xE14"

addr 0xE14 @asm  "pop {r3-r5, lr}"
label pc_0xE14
PC:u32 = 0xE14:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x10:u64))
tmp_lr_svc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r5:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r3:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R3:u32 = tmp_r3:u32
R4:u32 = tmp_r4:u32
R5:u32 = tmp_r5:u32
SP_SVC:u32 = tmp_sp_svc:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xE18"

addr 0xE18 @asm  "bx lr"
label pc_0xE18
PC:u32 = 0xE18:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0xE1C @asm  "push {r3-r5, lr}"
label pc_0xE1C
PC:u32 = 0xE1C:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF0:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R5:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF4:u64)) ,e_little]:u32 =R4:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF0:u64)) ,e_little]:u32 =R3:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xE20"

addr 0xE20 @asm  "mov r5, r0"
label pc_0xE20
PC:u32 = 0xE20:u32
tmp_r5:u32 = R0:u32
R5:u32 = tmp_r5:u32
jmp  "pc_0xE24"

addr 0xE24 @asm  "mov r4, #32"
label pc_0xE24
PC:u32 = 0xE24:u32
tmp_r4:u32 = low:u32(0x20:u64)
R4:u32 = tmp_r4:u32
jmp  "pc_0xE28"

addr 0xE28 @asm  "b +#20"
label pc_0xE28
PC:u32 = 0xE28:u32
jmp  "pc_0xE3C"

addr 0xE2C @asm  "tst r4, #3"
label pc_0xE2C
PC:u32 = 0xE2C:u32
tmp_n_flag:bool = low:bool(low:bool(((R4:u32 & low:u32(0x3:u64))) >> 0x1f:u32 ))
tmp_z_flag:bool = low:bool(((R4:u32 & low:u32(0x3:u64)) == low:u32(0x0:u64)))
N_FLAG:bool = tmp_n_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
jmp  "pc_0xE30"

addr 0xE30 @asm  "moveq r0, #95"
label pc_0xE30
PC:u32 = 0xE30:u32
TmpV_138:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_138:bool , "L_275" , "pc_0xE34"
label L_275
tmp_r0:u32 = low:u32(0x5F:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0xE34"

addr 0xE34 @asm  "bleq -#540"
label pc_0xE34
PC:u32 = 0xE34:u32
TmpV_139:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_139:bool , "L_277" , "pc_0xE38"
label L_277
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xE38"

addr 0xE38 @asm  "mov r5, r5, lsl #1"
label pc_0xE38
PC:u32 = 0xE38:u32
tmp_r5:u32 = (R5:u32 << low:u32(0x1:u64))
R5:u32 = tmp_r5:u32
jmp  "pc_0xE3C"

addr 0xE3C @asm  "cmp r5, #0"
label pc_0xE3C
PC:u32 = 0xE3C:u32
tmp_n_flag:bool = low:bool(low:bool((R5:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R5:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R5:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R5:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R5:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R5:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R5:u32) >> 0x1f:u32 ) & ~(low:bool((R5:u32) >> 0x1f:u32 ) == ((((extend:u64(R5:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xE40"

addr 0xE40 @asm  "movge r0, #48"
label pc_0xE40
PC:u32 = 0xE40:u32
TmpV_140:bool = low:bool( (N_FLAG:bool == V_FLAG:bool))
cjmp TmpV_140:bool , "L_279" , "pc_0xE44"
label L_279
tmp_r0:u32 = low:u32(0x30:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0xE44"

addr 0xE44 @asm  "movlt r0, #49"
label pc_0xE44
PC:u32 = 0xE44:u32
TmpV_141:bool = low:bool( ~(N_FLAG:bool == V_FLAG:bool))
cjmp TmpV_141:bool , "L_281" , "pc_0xE48"
label L_281
tmp_r0:u32 = low:u32(0x31:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0xE48"

addr 0xE48 @asm  "bl -#560"
label pc_0xE48
PC:u32 = 0xE48:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xC18"

addr 0xE4C @asm  "subs r4, r4, #1"
label pc_0xE4C
PC:u32 = 0xE4C:u32
tmp_r4:u32 = (R4:u32 + low:u32(0xFFFFFFFF:u64))
tmp_n_flag:bool = low:bool(low:bool(((R4:u32 + low:u32(0xFFFFFFFF:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R4:u32) + 0xFFFFFFFE:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R4:u32) + 0xFFFFFFFE:u64 + 0x1:u64) else ((extend:u64(R4:u32) + 0xFFFFFFFE:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R4:u32) + 0xFFFFFFFE:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R4:u32 + low:u32(0xFFFFFFFF:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R4:u32) >> 0x1f:u32 ) & ~(low:bool((R4:u32) >> 0x1f:u32 ) == ((((extend:u64(R4:u32) + 0xFFFFFFFE:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
R4:u32 = tmp_r4:u32
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xE50"

addr 0xE50 @asm  "bne -#36"
label pc_0xE50
PC:u32 = 0xE50:u32
TmpV_142:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_142:bool , "pc_0xE2C" , "pc_0xE54"

addr 0xE54 @asm  "pop {r3-r5, lr}"
label pc_0xE54
PC:u32 = 0xE54:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x10:u64))
tmp_lr_svc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r5:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r3:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R3:u32 = tmp_r3:u32
R4:u32 = tmp_r4:u32
R5:u32 = tmp_r5:u32
SP_SVC:u32 = tmp_sp_svc:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xE58"

addr 0xE58 @asm  "bx lr"
label pc_0xE58
PC:u32 = 0xE58:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0xE5C @asm  "push {r0-r3}"
label pc_0xE5C
PC:u32 = 0xE5C:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF0:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =R3:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R2:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF4:u64)) ,e_little]:u32 =R1:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF0:u64)) ,e_little]:u32 =R0:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xE60"

addr 0xE60 @asm  "push {r0-r2, r4, r5, lr}"
label pc_0xE60
PC:u32 = 0xE60:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFE8:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R5:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF4:u64)) ,e_little]:u32 =R4:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF0:u64)) ,e_little]:u32 =R2:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFEC:u64)) ,e_little]:u32 =R1:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFE8:u64)) ,e_little]:u32 =R0:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xE64"

addr 0xE64 @asm  "add r3, sp, #28"
label pc_0xE64
PC:u32 = 0xE64:u32
tmp_r3:u32 = (SP_SVC:u32 + low:u32(0x1C:u64))
R3:u32 = tmp_r3:u32
jmp  "pc_0xE68"

addr 0xE68 @asm  "ldr r5, [sp, #24]"
label pc_0xE68
PC:u32 = 0xE68:u32
tmp_r5:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x18:u64)),e_little]:u32
R5:u32 = tmp_r5:u32
jmp  "pc_0xE6C"

addr 0xE6C @asm  "str r3, [sp, #4]"
label pc_0xE6C
PC:u32 = 0xE6C:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0x4:u64)) ,e_little]:u32 =R3:u32
jmp  "pc_0xE70"

addr 0xE70 @asm  "ldrb r0, [r5]"
label pc_0xE70
PC:u32 = 0xE70:u32
r0:u32 = pad:u32(mem:?u32[R5:u32 ,e_little]:u8)
R0:u32 = tmp_r0:u32
jmp  "pc_0xE74"

addr 0xE74 @asm  "cmp r0, #0"
label pc_0xE74
PC:u32 = 0xE74:u32
tmp_n_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xE78"

addr 0xE78 @asm  "beq +#240"
label pc_0xE78
PC:u32 = 0xE78:u32
TmpV_143:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_143:bool , "pc_0xF68" , "pc_0xE7C"

addr 0xE7C @asm  "cmp r0, #37"
label pc_0xE7C
PC:u32 = 0xE7C:u32
tmp_n_flag:bool = low:bool(low:bool(((R0:u32 + low:u32(0xFFFFFFDB:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFDA:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFDA:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFDA:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFDA:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R0:u32 + low:u32(0xFFFFFFDB:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFDA:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xE80"

addr 0xE80 @asm  "add r5, r5, #1"
label pc_0xE80
PC:u32 = 0xE80:u32
tmp_r5:u32 = (R5:u32 + low:u32(0x1:u64))
R5:u32 = tmp_r5:u32
jmp  "pc_0xE84"

addr 0xE84 @asm  "bne +#220"
label pc_0xE84
PC:u32 = 0xE84:u32
TmpV_144:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_144:bool , "pc_0xF60" , "pc_0xE88"

addr 0xE88 @asm  "ldrb r4, [r5], #1"
label pc_0xE88
PC:u32 = 0xE88:u32
tmp_r5:u32 = (R5:u32 + low:u32(0x1:u64))
r4:u32 = pad:u32(mem:?u32[R5:u32 ,e_little]:u8)
R4:u32 = tmp_r4:u32
R5:u32 = tmp_r5:u32
jmp  "pc_0xE8C"

addr 0xE8C @asm  "cmp r4, #0"
label pc_0xE8C
PC:u32 = 0xE8C:u32
tmp_n_flag:bool = low:bool(low:bool((R4:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R4:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R4:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R4:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R4:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R4:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R4:u32) >> 0x1f:u32 ) & ~(low:bool((R4:u32) >> 0x1f:u32 ) == ((((extend:u64(R4:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xE90"

addr 0xE90 @asm  "bne +#16"
label pc_0xE90
PC:u32 = 0xE90:u32
TmpV_145:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_145:bool , "pc_0xEA0" , "pc_0xE94"

addr 0xE94 @asm  "mov r0, r4"
label pc_0xE94
PC:u32 = 0xE94:u32
tmp_r0:u32 = R4:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xE98"

addr 0xE98 @asm  "bl -#640"
label pc_0xE98
PC:u32 = 0xE98:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xC18"

addr 0xE9C @asm  "b +#204"
label pc_0xE9C
PC:u32 = 0xE9C:u32
jmp  "pc_0xF68"

addr 0xEA0 @asm  "cmp r4, #100"
label pc_0xEA0
PC:u32 = 0xEA0:u32
tmp_n_flag:bool = low:bool(low:bool(((R4:u32 + low:u32(0xFFFFFF9C:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R4:u32) + 0xFFFFFF9B:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R4:u32) + 0xFFFFFF9B:u64 + 0x1:u64) else ((extend:u64(R4:u32) + 0xFFFFFF9B:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R4:u32) + 0xFFFFFF9B:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R4:u32 + low:u32(0xFFFFFF9C:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R4:u32) >> 0x1f:u32 ) & ~(low:bool((R4:u32) >> 0x1f:u32 ) == ((((extend:u64(R4:u32) + 0xFFFFFF9B:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xEA4"

addr 0xEA4 @asm  "beq +#104"
label pc_0xEA4
PC:u32 = 0xEA4:u32
TmpV_146:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_146:bool , "pc_0xF0C" , "pc_0xEA8"

addr 0xEA8 @asm  "bhi +#28"
label pc_0xEA8
PC:u32 = 0xEA8:u32
TmpV_147:bool = low:bool( C_FLAG:bool & ~Z_FLAG:bool)
cjmp TmpV_147:bool , "pc_0xEC4" , "pc_0xEAC"

addr 0xEAC @asm  "cmp r4, #98"
label pc_0xEAC
PC:u32 = 0xEAC:u32
tmp_n_flag:bool = low:bool(low:bool(((R4:u32 + low:u32(0xFFFFFF9E:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R4:u32) + 0xFFFFFF9D:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R4:u32) + 0xFFFFFF9D:u64 + 0x1:u64) else ((extend:u64(R4:u32) + 0xFFFFFF9D:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R4:u32) + 0xFFFFFF9D:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R4:u32 + low:u32(0xFFFFFF9E:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R4:u32) >> 0x1f:u32 ) & ~(low:bool((R4:u32) >> 0x1f:u32 ) == ((((extend:u64(R4:u32) + 0xFFFFFF9D:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xEB0"

addr 0xEB0 @asm  "beq +#140"
label pc_0xEB0
PC:u32 = 0xEB0:u32
TmpV_148:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_148:bool , "pc_0xF3C" , "pc_0xEB4"

addr 0xEB4 @asm  "bhi +#44"
label pc_0xEB4
PC:u32 = 0xEB4:u32
TmpV_149:bool = low:bool( C_FLAG:bool & ~Z_FLAG:bool)
cjmp TmpV_149:bool , "pc_0xEE0" , "pc_0xEB8"

addr 0xEB8 @asm  "cmp r4, #37"
label pc_0xEB8
PC:u32 = 0xEB8:u32
tmp_n_flag:bool = low:bool(low:bool(((R4:u32 + low:u32(0xFFFFFFDB:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R4:u32) + 0xFFFFFFDA:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R4:u32) + 0xFFFFFFDA:u64 + 0x1:u64) else ((extend:u64(R4:u32) + 0xFFFFFFDA:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R4:u32) + 0xFFFFFFDA:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R4:u32 + low:u32(0xFFFFFFDB:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R4:u32) >> 0x1f:u32 ) & ~(low:bool((R4:u32) >> 0x1f:u32 ) == ((((extend:u64(R4:u32) + 0xFFFFFFDA:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xEBC"

addr 0xEBC @asm  "bne +#152"
label pc_0xEBC
PC:u32 = 0xEBC:u32
TmpV_150:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_150:bool , "pc_0xF54" , "pc_0xEC0"

addr 0xEC0 @asm  "b +#156"
label pc_0xEC0
PC:u32 = 0xEC0:u32
jmp  "pc_0xF5C"

addr 0xEC4 @asm  "cmp r4, #115"
label pc_0xEC4
PC:u32 = 0xEC4:u32
tmp_n_flag:bool = low:bool(low:bool(((R4:u32 + low:u32(0xFFFFFF8D:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R4:u32) + 0xFFFFFF8C:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R4:u32) + 0xFFFFFF8C:u64 + 0x1:u64) else ((extend:u64(R4:u32) + 0xFFFFFF8C:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R4:u32) + 0xFFFFFF8C:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R4:u32 + low:u32(0xFFFFFF8D:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R4:u32) >> 0x1f:u32 ) & ~(low:bool((R4:u32) >> 0x1f:u32 ) == ((((extend:u64(R4:u32) + 0xFFFFFF8C:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xEC8"

addr 0xEC8 @asm  "beq +#44"
label pc_0xEC8
PC:u32 = 0xEC8:u32
TmpV_151:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_151:bool , "pc_0xEF4" , "pc_0xECC"

addr 0xECC @asm  "cmp r4, #120"
label pc_0xECC
PC:u32 = 0xECC:u32
tmp_n_flag:bool = low:bool(low:bool(((R4:u32 + low:u32(0xFFFFFF88:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R4:u32) + 0xFFFFFF87:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R4:u32) + 0xFFFFFF87:u64 + 0x1:u64) else ((extend:u64(R4:u32) + 0xFFFFFF87:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R4:u32) + 0xFFFFFF87:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R4:u32 + low:u32(0xFFFFFF88:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R4:u32) >> 0x1f:u32 ) & ~(low:bool((R4:u32) >> 0x1f:u32 ) == ((((extend:u64(R4:u32) + 0xFFFFFF87:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xED0"

addr 0xED0 @asm  "beq +#84"
label pc_0xED0
PC:u32 = 0xED0:u32
TmpV_152:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_152:bool , "pc_0xF24" , "pc_0xED4"

addr 0xED4 @asm  "cmp r4, #105"
label pc_0xED4
PC:u32 = 0xED4:u32
tmp_n_flag:bool = low:bool(low:bool(((R4:u32 + low:u32(0xFFFFFF97:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R4:u32) + 0xFFFFFF96:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R4:u32) + 0xFFFFFF96:u64 + 0x1:u64) else ((extend:u64(R4:u32) + 0xFFFFFF96:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R4:u32) + 0xFFFFFF96:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R4:u32 + low:u32(0xFFFFFF97:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R4:u32) >> 0x1f:u32 ) & ~(low:bool((R4:u32) >> 0x1f:u32 ) == ((((extend:u64(R4:u32) + 0xFFFFFF96:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xED8"

addr 0xED8 @asm  "bne +#124"
label pc_0xED8
PC:u32 = 0xED8:u32
TmpV_153:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_153:bool , "pc_0xF54" , "pc_0xEDC"

addr 0xEDC @asm  "b +#48"
label pc_0xEDC
PC:u32 = 0xEDC:u32
jmp  "pc_0xF0C"

addr 0xEE0 @asm  "ldr r3, [sp, #4]"
label pc_0xEE0
PC:u32 = 0xEE0:u32
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0xEE4"

addr 0xEE4 @asm  "add r2, r3, #4"
label pc_0xEE4
PC:u32 = 0xEE4:u32
tmp_r2:u32 = (R3:u32 + low:u32(0x4:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0xEE8"

addr 0xEE8 @asm  "str r2, [sp, #4]"
label pc_0xEE8
PC:u32 = 0xEE8:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0x4:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0xEEC"

addr 0xEEC @asm  "ldr r0, [r3]"
label pc_0xEEC
PC:u32 = 0xEEC:u32
tmp_r0:u32 = mem:?u32[R3:u32,e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xEF0"

addr 0xEF0 @asm  "b +#112"
label pc_0xEF0
PC:u32 = 0xEF0:u32
jmp  "pc_0xF60"

addr 0xEF4 @asm  "ldr r3, [sp, #4]"
label pc_0xEF4
PC:u32 = 0xEF4:u32
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0xEF8"

addr 0xEF8 @asm  "add r2, r3, #4"
label pc_0xEF8
PC:u32 = 0xEF8:u32
tmp_r2:u32 = (R3:u32 + low:u32(0x4:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0xEFC"

addr 0xEFC @asm  "ldr r0, [r3]"
label pc_0xEFC
PC:u32 = 0xEFC:u32
tmp_r0:u32 = mem:?u32[R3:u32,e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xF00"

addr 0xF00 @asm  "str r2, [sp, #4]"
label pc_0xF00
PC:u32 = 0xF00:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0x4:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0xF04"

addr 0xF04 @asm  "bl -#452"
label pc_0xF04
PC:u32 = 0xF04:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xD40"

addr 0xF08 @asm  "b -#152"
label pc_0xF08
PC:u32 = 0xF08:u32
jmp  "pc_0xE70"

addr 0xF0C @asm  "ldr r3, [sp, #4]"
label pc_0xF0C
PC:u32 = 0xF0C:u32
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0xF10"

addr 0xF10 @asm  "add r2, r3, #4"
label pc_0xF10
PC:u32 = 0xF10:u32
tmp_r2:u32 = (R3:u32 + low:u32(0x4:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0xF14"

addr 0xF14 @asm  "ldr r0, [r3]"
label pc_0xF14
PC:u32 = 0xF14:u32
tmp_r0:u32 = mem:?u32[R3:u32,e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xF18"

addr 0xF18 @asm  "str r2, [sp, #4]"
label pc_0xF18
PC:u32 = 0xF18:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0x4:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0xF1C"

addr 0xF1C @asm  "bl -#440"
label pc_0xF1C
PC:u32 = 0xF1C:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xD64"

addr 0xF20 @asm  "b -#176"
label pc_0xF20
PC:u32 = 0xF20:u32
jmp  "pc_0xE70"

addr 0xF24 @asm  "ldr r3, [sp, #4]"
label pc_0xF24
PC:u32 = 0xF24:u32
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0xF28"

addr 0xF28 @asm  "add r2, r3, #4"
label pc_0xF28
PC:u32 = 0xF28:u32
tmp_r2:u32 = (R3:u32 + low:u32(0x4:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0xF2C"

addr 0xF2C @asm  "ldr r0, [r3]"
label pc_0xF2C
PC:u32 = 0xF2C:u32
tmp_r0:u32 = mem:?u32[R3:u32,e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xF30"

addr 0xF30 @asm  "str r2, [sp, #4]"
label pc_0xF30
PC:u32 = 0xF30:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0x4:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0xF34"

addr 0xF34 @asm  "bl -#336"
label pc_0xF34
PC:u32 = 0xF34:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xDE4"

addr 0xF38 @asm  "b -#200"
label pc_0xF38
PC:u32 = 0xF38:u32
jmp  "pc_0xE70"

addr 0xF3C @asm  "ldr r3, [sp, #4]"
label pc_0xF3C
PC:u32 = 0xF3C:u32
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0xF40"

addr 0xF40 @asm  "add r2, r3, #4"
label pc_0xF40
PC:u32 = 0xF40:u32
tmp_r2:u32 = (R3:u32 + low:u32(0x4:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0xF44"

addr 0xF44 @asm  "ldr r0, [r3]"
label pc_0xF44
PC:u32 = 0xF44:u32
tmp_r0:u32 = mem:?u32[R3:u32,e_little]:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xF48"

addr 0xF48 @asm  "str r2, [sp, #4]"
label pc_0xF48
PC:u32 = 0xF48:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0x4:u64)) ,e_little]:u32 =R2:u32
jmp  "pc_0xF4C"

addr 0xF4C @asm  "bl -#304"
label pc_0xF4C
PC:u32 = 0xF4C:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xE1C"

addr 0xF50 @asm  "b -#224"
label pc_0xF50
PC:u32 = 0xF50:u32
jmp  "pc_0xE70"

addr 0xF54 @asm  "mov r0, #37"
label pc_0xF54
PC:u32 = 0xF54:u32
tmp_r0:u32 = low:u32(0x25:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0xF58"

addr 0xF58 @asm  "bl -#832"
label pc_0xF58
PC:u32 = 0xF58:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xC18"

addr 0xF5C @asm  "mov r0, r4"
label pc_0xF5C
PC:u32 = 0xF5C:u32
tmp_r0:u32 = R4:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xF60"

addr 0xF60 @asm  "bl -#840"
label pc_0xF60
PC:u32 = 0xF60:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xC18"

addr 0xF64 @asm  "b -#244"
label pc_0xF64
PC:u32 = 0xF64:u32
jmp  "pc_0xE70"

addr 0xF68 @asm  "pop {r1-r5, lr}"
label pc_0xF68
PC:u32 = 0xF68:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x18:u64))
tmp_lr_svc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x14:u64)),e_little]:u32
tmp_r5:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x10:u64)),e_little]:u32
tmp_r4:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0xC:u64)),e_little]:u32
tmp_r3:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r2:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r1:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R1:u32 = tmp_r1:u32
R2:u32 = tmp_r2:u32
R3:u32 = tmp_r3:u32
R4:u32 = tmp_r4:u32
R5:u32 = tmp_r5:u32
SP_SVC:u32 = tmp_sp_svc:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xF6C"

addr 0xF6C @asm  "add sp, sp, #16"
label pc_0xF6C
PC:u32 = 0xF6C:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0x10:u64))
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0xF70"

addr 0xF70 @asm  "bx lr"
label pc_0xF70
PC:u32 = 0xF70:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0xF74 @asm  "cmp r1, #0"
label pc_0xF74
PC:u32 = 0xF74:u32
tmp_n_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R1:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xF78"

addr 0xF78 @asm  "beq +#276"
label pc_0xF78
PC:u32 = 0xF78:u32
TmpV_154:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_154:bool , "pc_0x108C" , "pc_0xF7C"


addr 0xF7C @asm  "eor r12, r0, r1"
label pc_0xF7C
PC:u32 = 0xF7C:u32
tmp_r12:u32 = (R0:u32^R1:u32)
R12:u32 = tmp_r12:u32
jmp  "pc_0xF80"

addr 0xF80 @asm  "rsbmi r1, r1, #0"
label pc_0xF80
PC:u32 = 0xF80:u32
TmpV_155:bool = low:bool( N_FLAG:bool)
cjmp TmpV_155:bool , "L_309" , "pc_0xF84"
label L_309
tmp_r1:u32 =  -R1:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0xF84"

addr 0xF84 @asm  "subs r2, r1, #1"
label pc_0xF84
PC:u32 = 0xF84:u32
tmp_r2:u32 = (R1:u32 + low:u32(0xFFFFFFFF:u64))
tmp_n_flag:bool = low:bool(low:bool(((R1:u32 + low:u32(0xFFFFFFFF:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFFFFFE:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFFFFFE:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFFFFFE:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFFFFFE:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R1:u32 + low:u32(0xFFFFFFFF:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFFFFFE:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
R2:u32 = tmp_r2:u32
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xF88"

addr 0xF88 @asm  "beq +#164"
label pc_0xF88
PC:u32 = 0xF88:u32
TmpV_156:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_156:bool , "pc_0x102C" , "pc_0xF8C"

addr 0xF8C @asm  "movs r3, r0"
label pc_0xF8C
PC:u32 = 0xF8C:u32
tmp_r3:u32 = R0:u32
tmp_n_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ))
tmp_z_flag:bool = low:bool((R0:u32 == low:u32(0x0:u64)))
R3:u32 = tmp_r3:u32
N_FLAG:bool = tmp_n_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
jmp  "pc_0xF90"

addr 0xF90 @asm  "rsbmi r3, r0, #0"
label pc_0xF90
PC:u32 = 0xF90:u32
TmpV_157:bool = low:bool( N_FLAG:bool)
cjmp TmpV_157:bool , "L_313" , "pc_0xF94"
label L_313
tmp_r3:u32 =  -R0:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0xF94"

addr 0xF94 @asm  "cmp r3, r1"
label pc_0xF94
PC:u32 = 0xF94:u32
tmp_n_flag:bool = low:bool(low:bool(((R3:u32 +  -R1:u32)) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R3:u32) + extend:u64( ~R1:u32) + 0x1:u64) < 0x100000000:u64 then (extend:u64(R3:u32) + extend:u64( ~R1:u32) + 0x1:u64) else ((extend:u64(R3:u32) + extend:u64( ~R1:u32) + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R3:u32) + extend:u64( ~R1:u32) + 0x1:u64)))
tmp_z_flag:bool = low:bool((R3:u32 == R1:u32))
tmp_v_flag:bool = low:bool((low:bool((R3:u32) >> 0x1f:u32 ) == low:bool(( ~R1:u32) >> 0x1f:u32 )) & ~(low:bool((R3:u32) >> 0x1f:u32 ) == ((((extend:u64(R3:u32) + extend:u64( ~R1:u32) + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xF98"

addr 0xF98 @asm  "bls +#160"
label pc_0xF98
PC:u32 = 0xF98:u32
jmp "lift_error"
cjmp TmpV_158:bool , "pc_0x1038" , "pc_0xF9C"

addr 0xF9C @asm  "tst r1, r2"
label pc_0xF9C
PC:u32 = 0xF9C:u32
tmp_n_flag:bool = low:bool(low:bool(((R1:u32 & R2:u32)) >> 0x1f:u32 ))
tmp_z_flag:bool = low:bool(((R1:u32 & R2:u32) == low:u32(0x0:u64)))
N_FLAG:bool = tmp_n_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
jmp  "pc_0xFA0"

addr 0xFA0 @asm  "beq +#168"
label pc_0xFA0
PC:u32 = 0xFA0:u32
TmpV_159:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_159:bool , "pc_0x1048" , "pc_0xFA4"

addr 0xFA4 @asm  "tst r1, #0xE0000000"
label pc_0xFA4
PC:u32 = 0xFA4:u32
tmp_n_flag:bool = low:bool(low:bool(((R1:u32 & low:u32(0xE0000000:u64))) >> 0x1f:u32 ))
jmp "lift_error"
tmp_z_flag:bool = low:bool(((R1:u32 & low:u32(0xE0000000:u64)) == low:u32(0x0:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
jmp  "pc_0xFA8"

addr 0xFA8 @asm  "moveq r1, r1, lsl #3"
label pc_0xFA8
PC:u32 = 0xFA8:u32
TmpV_160:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_160:bool , "L_319" , "pc_0xFAC"
label L_319
tmp_r1:u32 = (R1:u32 << low:u32(0x3:u64))
R1:u32 = tmp_r1:u32
jmp  "pc_0xFAC"

addr 0xFAC @asm  "moveq r2, #8"
label pc_0xFAC
PC:u32 = 0xFAC:u32
TmpV_161:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_161:bool , "L_321" , "pc_0xFB0"
label L_321
tmp_r2:u32 = low:u32(0x8:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0xFB0"

addr 0xFB0 @asm  "movne r2, #1"
label pc_0xFB0
PC:u32 = 0xFB0:u32
TmpV_162:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_162:bool , "L_323" , "pc_0xFB4"
label L_323
tmp_r2:u32 = low:u32(0x1:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0xFB4"

addr 0xFB4 @asm  "cmp r1, #0x10000000"
label pc_0xFB4
PC:u32 = 0xFB4:u32
tmp_n_flag:bool = low:bool(low:bool(((R1:u32 + low:u32(0xF0000000:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xEFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xEFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xEFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xEFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R1:u32 + low:u32(0xF0000000:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xEFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xFB8"

addr 0xFB8 @asm  "cmpcc r1, r3"
label pc_0xFB8
PC:u32 = 0xFB8:u32
TmpV_163:bool = low:bool( ~C_FLAG:bool)
cjmp TmpV_163:bool , "L_325" , "pc_0xFBC"
label L_325
tmp_n_flag:bool = low:bool(low:bool(((R1:u32 +  -R3:u32)) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + extend:u64( ~R3:u32) + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + extend:u64( ~R3:u32) + 0x1:u64) else ((extend:u64(R1:u32) + extend:u64( ~R3:u32) + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + extend:u64( ~R3:u32) + 0x1:u64)))
tmp_z_flag:bool = low:bool((R1:u32 == R3:u32))
tmp_v_flag:bool = low:bool((low:bool((R1:u32) >> 0x1f:u32 ) == low:bool(( ~R3:u32) >> 0x1f:u32 )) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + extend:u64( ~R3:u32) + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xFBC"

addr 0xFBC @asm  "movcc r1, r1, lsl #4"
label pc_0xFBC
PC:u32 = 0xFBC:u32
TmpV_164:bool = low:bool( ~C_FLAG:bool)
cjmp TmpV_164:bool , "L_327" , "pc_0xFC0"
label L_327
tmp_r1:u32 = (R1:u32 << low:u32(0x4:u64))
R1:u32 = tmp_r1:u32
jmp  "pc_0xFC0"

addr 0xFC0 @asm  "movcc r2, r2, lsl #4"
label pc_0xFC0
PC:u32 = 0xFC0:u32
TmpV_165:bool = low:bool( ~C_FLAG:bool)
cjmp TmpV_165:bool , "L_329" , "pc_0xFC4"
label L_329
tmp_r2:u32 = (R2:u32 << low:u32(0x4:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0xFC4"

addr 0xFC4 @asm  "bcc -#16"
label pc_0xFC4
PC:u32 = 0xFC4:u32
TmpV_166:bool = low:bool( ~C_FLAG:bool)
cjmp TmpV_166:bool , "pc_0xFB4" , "pc_0xFC8"

addr 0xFC8 @asm  "cmp r1, #0x80000000"
label pc_0xFC8
PC:u32 = 0xFC8:u32
tmp_n_flag:bool = low:bool(low:bool(((R1:u32 + low:u32(0x80000000:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0x7FFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0x7FFFFFFF:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0x7FFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0x7FFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R1:u32 + low:u32(0x80000000:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(~low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0x7FFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xFCC"

addr 0xFCC @asm  "cmpcc r1, r3"
label pc_0xFCC
PC:u32 = 0xFCC:u32
TmpV_167:bool = low:bool( ~C_FLAG:bool)
cjmp TmpV_167:bool , "L_333" , "pc_0xFD0"
label L_333
tmp_n_flag:bool = low:bool(low:bool(((R1:u32 +  -R3:u32)) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + extend:u64( ~R3:u32) + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + extend:u64( ~R3:u32) + 0x1:u64) else ((extend:u64(R1:u32) + extend:u64( ~R3:u32) + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + extend:u64( ~R3:u32) + 0x1:u64)))
tmp_z_flag:bool = low:bool((R1:u32 == R3:u32))
tmp_v_flag:bool = low:bool((low:bool((R1:u32) >> 0x1f:u32 ) == low:bool(( ~R3:u32) >> 0x1f:u32 )) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + extend:u64( ~R3:u32) + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xFD0"

addr 0xFD0 @asm  "movcc r1, r1, lsl #1"
label pc_0xFD0
PC:u32 = 0xFD0:u32
TmpV_168:bool = low:bool( ~C_FLAG:bool)
cjmp TmpV_168:bool , "L_335" , "pc_0xFD4"
label L_335
tmp_r1:u32 = (R1:u32 << low:u32(0x1:u64))
R1:u32 = tmp_r1:u32
jmp  "pc_0xFD4"

addr 0xFD4 @asm  "movcc r2, r2, lsl #1"
label pc_0xFD4
PC:u32 = 0xFD4:u32
TmpV_169:bool = low:bool( ~C_FLAG:bool)
cjmp TmpV_169:bool , "L_337" , "pc_0xFD8"
label L_337
tmp_r2:u32 = (R2:u32 << low:u32(0x1:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0xFD8"

addr 0xFD8 @asm  "bcc -#16"
label pc_0xFD8
PC:u32 = 0xFD8:u32
TmpV_170:bool = low:bool( ~C_FLAG:bool)
cjmp TmpV_170:bool , "pc_0xFC8" , "pc_0xFDC"

addr 0xFDC @asm  "mov r0, #0"
label pc_0xFDC
PC:u32 = 0xFDC:u32
tmp_r0:u32 = low:u32(0x0:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0xFE0"

addr 0xFE0 @asm  "cmp r3, r1"
label pc_0xFE0
PC:u32 = 0xFE0:u32
tmp_n_flag:bool = low:bool(low:bool(((R3:u32 +  -R1:u32)) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R3:u32) + extend:u64( ~R1:u32) + 0x1:u64) < 0x100000000:u64 then (extend:u64(R3:u32) + extend:u64( ~R1:u32) + 0x1:u64) else ((extend:u64(R3:u32) + extend:u64( ~R1:u32) + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R3:u32) + extend:u64( ~R1:u32) + 0x1:u64)))
tmp_z_flag:bool = low:bool((R3:u32 == R1:u32))
tmp_v_flag:bool = low:bool((low:bool((R3:u32) >> 0x1f:u32 ) == low:bool(( ~R1:u32) >> 0x1f:u32 )) & ~(low:bool((R3:u32) >> 0x1f:u32 ) == ((((extend:u64(R3:u32) + extend:u64( ~R1:u32) + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xFE4"

addr 0xFE4 @asm  "subcs r3, r3, r1"
label pc_0xFE4
PC:u32 = 0xFE4:u32
TmpV_171:bool = low:bool( C_FLAG:bool)
cjmp TmpV_171:bool , "L_341" , "pc_0xFE8"
label L_341
tmp_r3:u32 = (R3:u32 +  -R1:u32)
R3:u32 = tmp_r3:u32
jmp  "pc_0xFE8"

addr 0xFE8 @asm  "orrcs r0, r0, r2"
label pc_0xFE8
PC:u32 = 0xFE8:u32
TmpV_172:bool = low:bool( C_FLAG:bool)
cjmp TmpV_172:bool , "L_343" , "pc_0xFEC"
label L_343
tmp_r0:u32 = R0:u32 | R2:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xFEC"

addr 0xFEC @asm  "cmp r3, r1, lsr #1"
label pc_0xFEC
PC:u32 = 0xFEC:u32
tmp_n_flag:bool = low:bool(low:bool(((R3:u32 +  -(R1:u32 >> low:u32(0x1:u64)))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R3:u32) + extend:u64( ~(R1:u32 >> low:u32(0x1:u64))) + 0x1:u64) < 0x100000000:u64 then (extend:u64(R3:u32) + extend:u64( ~(R1:u32 >> low:u32(0x1:u64))) + 0x1:u64) else ((extend:u64(R3:u32) + extend:u64( ~(R1:u32 >> low:u32(0x1:u64))) + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R3:u32) + extend:u64( ~(R1:u32 >> low:u32(0x1:u64))) + 0x1:u64)))
tmp_z_flag:bool = low:bool((R3:u32 == (R1:u32 >> low:u32(0x1:u64))))
tmp_v_flag:bool = low:bool((low:bool((R3:u32) >> 0x1f:u32 ) == low:bool(( ~(R1:u32 >> low:u32(0x1:u64))) >> 0x1f:u32 )) & ~(low:bool((R3:u32) >> 0x1f:u32 ) == ((((extend:u64(R3:u32) + extend:u64( ~(R1:u32 >> low:u32(0x1:u64))) + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xFF0"

addr 0xFF0 @asm  "subcs r3, r3, r1, lsr #1"
label pc_0xFF0
PC:u32 = 0xFF0:u32
TmpV_173:bool = low:bool( C_FLAG:bool)
cjmp TmpV_173:bool , "L_345" , "pc_0xFF4"
label L_345
tmp_r3:u32 = (R3:u32 +  -(R1:u32 >> low:u32(0x1:u64)))
R3:u32 = tmp_r3:u32
jmp  "pc_0xFF4"

addr 0xFF4 @asm  "orrcs r0, r0, r2, lsr #1"
label pc_0xFF4
PC:u32 = 0xFF4:u32
TmpV_174:bool = low:bool( C_FLAG:bool)
cjmp TmpV_174:bool , "L_347" , "pc_0xFF8"
label L_347
tmp_r0:u32 = R0:u32 | (R2:u32 >> low:u32(0x1:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0xFF8"

addr 0xFF8 @asm  "cmp r3, r1, lsr #2"
label pc_0xFF8
PC:u32 = 0xFF8:u32
tmp_n_flag:bool = low:bool(low:bool(((R3:u32 +  -(R1:u32 >> low:u32(0x2:u64)))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R3:u32) + extend:u64( ~(R1:u32 >> low:u32(0x2:u64))) + 0x1:u64) < 0x100000000:u64 then (extend:u64(R3:u32) + extend:u64( ~(R1:u32 >> low:u32(0x2:u64))) + 0x1:u64) else ((extend:u64(R3:u32) + extend:u64( ~(R1:u32 >> low:u32(0x2:u64))) + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R3:u32) + extend:u64( ~(R1:u32 >> low:u32(0x2:u64))) + 0x1:u64)))
tmp_z_flag:bool = low:bool((R3:u32 == (R1:u32 >> low:u32(0x2:u64))))
tmp_v_flag:bool = low:bool((low:bool((R3:u32) >> 0x1f:u32 ) == low:bool(( ~(R1:u32 >> low:u32(0x2:u64))) >> 0x1f:u32 )) & ~(low:bool((R3:u32) >> 0x1f:u32 ) == ((((extend:u64(R3:u32) + extend:u64( ~(R1:u32 >> low:u32(0x2:u64))) + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xFFC"

addr 0xFFC @asm  "subcs r3, r3, r1, lsr #2"
label pc_0xFFC
PC:u32 = 0xFFC:u32
TmpV_175:bool = low:bool( C_FLAG:bool)
cjmp TmpV_175:bool , "L_349" , "pc_0x1000"
label L_349
tmp_r3:u32 = (R3:u32 +  -(R1:u32 >> low:u32(0x2:u64)))
R3:u32 = tmp_r3:u32
jmp  "pc_0x1000"

addr 0x1000 @asm  "orrcs r0, r0, r2, lsr #2"
label pc_0x1000
PC:u32 = 0x1000:u32
TmpV_176:bool = low:bool( C_FLAG:bool)
cjmp TmpV_176:bool , "L_351" , "pc_0x1004"
label L_351
tmp_r0:u32 = R0:u32 | (R2:u32 >> low:u32(0x2:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0x1004"

addr 0x1004 @asm  "cmp r3, r1, lsr #3"
label pc_0x1004
PC:u32 = 0x1004:u32
tmp_n_flag:bool = low:bool(low:bool(((R3:u32 +  -(R1:u32 >> low:u32(0x3:u64)))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R3:u32) + extend:u64( ~(R1:u32 >> low:u32(0x3:u64))) + 0x1:u64) < 0x100000000:u64 then (extend:u64(R3:u32) + extend:u64( ~(R1:u32 >> low:u32(0x3:u64))) + 0x1:u64) else ((extend:u64(R3:u32) + extend:u64( ~(R1:u32 >> low:u32(0x3:u64))) + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R3:u32) + extend:u64( ~(R1:u32 >> low:u32(0x3:u64))) + 0x1:u64)))
tmp_z_flag:bool = low:bool((R3:u32 == (R1:u32 >> low:u32(0x3:u64))))
tmp_v_flag:bool = low:bool((low:bool((R3:u32) >> 0x1f:u32 ) == low:bool(( ~(R1:u32 >> low:u32(0x3:u64))) >> 0x1f:u32 )) & ~(low:bool((R3:u32) >> 0x1f:u32 ) == ((((extend:u64(R3:u32) + extend:u64( ~(R1:u32 >> low:u32(0x3:u64))) + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x1008"

addr 0x1008 @asm  "subcs r3, r3, r1, lsr #3"
label pc_0x1008
PC:u32 = 0x1008:u32
TmpV_177:bool = low:bool( C_FLAG:bool)
cjmp TmpV_177:bool , "L_353" , "pc_0x100C"
label L_353
tmp_r3:u32 = (R3:u32 +  -(R1:u32 >> low:u32(0x3:u64)))
R3:u32 = tmp_r3:u32
jmp  "pc_0x100C"

addr 0x100C @asm  "orrcs r0, r0, r2, lsr #3"
label pc_0x100C
PC:u32 = 0x100C:u32
TmpV_178:bool = low:bool( C_FLAG:bool)
cjmp TmpV_178:bool , "L_355" , "pc_0x1010"
label L_355
tmp_r0:u32 = R0:u32 | (R2:u32 >> low:u32(0x3:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0x1010"

addr 0x1010 @asm  "cmp r3, #0"
label pc_0x1010
PC:u32 = 0x1010:u32
tmp_n_flag:bool = low:bool(low:bool((R3:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R3:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R3:u32) >> 0x1f:u32 ) & ~(low:bool((R3:u32) >> 0x1f:u32 ) == ((((extend:u64(R3:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x1014"

addr 0x1014 @asm  "movsne r2, r2, lsr #4"
label pc_0x1014
PC:u32 = 0x1014:u32
TmpV_179:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_179:bool , "L_357" , "pc_0x1018"
label L_357
tmp_r2:u32 = (R2:u32 >> low:u32(0x4:u64))
tmp_n_flag:bool = low:bool(low:bool(((R2:u32 >> low:u32(0x4:u64))) >> 0x1f:u32 ))
jmp "lift_error"
tmp_z_flag:bool = low:bool(((R2:u32 >> low:u32(0x4:u64)) == low:u32(0x0:u64)))
R2:u32 = tmp_r2:u32
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
jmp  "pc_0x1018"

addr 0x1018 @asm  "movne r1, r1, lsr #4"
label pc_0x1018
PC:u32 = 0x1018:u32
TmpV_180:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_180:bool , "L_359" , "pc_0x101C"
label L_359
tmp_r1:u32 = (R1:u32 >> low:u32(0x4:u64))
R1:u32 = tmp_r1:u32
jmp  "pc_0x101C"

addr 0x101C @asm  "bne -#60"
label pc_0x101C
PC:u32 = 0x101C:u32
TmpV_181:bool = low:bool( ~Z_FLAG:bool)
cjmp TmpV_181:bool , "pc_0xFE0" , "pc_0x1020"

addr 0x1020 @asm  "cmp r12, #0"
label pc_0x1020
PC:u32 = 0x1020:u32
tmp_n_flag:bool = low:bool(low:bool((R12:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R12:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R12:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R12:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R12:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R12:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R12:u32) >> 0x1f:u32 ) & ~(low:bool((R12:u32) >> 0x1f:u32 ) == ((((extend:u64(R12:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x1024"

addr 0x1024 @asm  "rsbmi r0, r0, #0"
label pc_0x1024
PC:u32 = 0x1024:u32
TmpV_182:bool = low:bool( N_FLAG:bool)
cjmp TmpV_182:bool , "L_363" , "pc_0x1028"
label L_363
tmp_r0:u32 =  -R0:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x1028"

addr 0x1028 @asm  "bx lr"
label pc_0x1028
PC:u32 = 0x1028:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x102C @asm  "teq r12, r0"
label pc_0x102C
PC:u32 = 0x102C:u32
tmp_n_flag:bool = low:bool(low:bool(((R12:u32^R0:u32)) >> 0x1f:u32 ))
tmp_z_flag:bool = low:bool(((R12:u32^R0:u32) == low:u32(0x0:u64)))
N_FLAG:bool = tmp_n_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
jmp  "pc_0x1030"

addr 0x1030 @asm  "rsbmi r0, r0, #0"
label pc_0x1030
PC:u32 = 0x1030:u32
TmpV_183:bool = low:bool( N_FLAG:bool)
cjmp TmpV_183:bool , "L_365" , "pc_0x1034"
label L_365
tmp_r0:u32 =  -R0:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x1034"

addr 0x1034 @asm  "bx lr"
label pc_0x1034
PC:u32 = 0x1034:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x1038 @asm  "movcc r0, #0"
label pc_0x1038
PC:u32 = 0x1038:u32
TmpV_184:bool = low:bool( ~C_FLAG:bool)
cjmp TmpV_184:bool , "L_367" , "pc_0x103C"
label L_367
tmp_r0:u32 = low:u32(0x0:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x103C"

addr 0x103C @asm  "moveq r0, r12, asr #31"
label pc_0x103C
PC:u32 = 0x103C:u32
TmpV_185:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_185:bool , "L_369" , "pc_0x1040"
label L_369
tmp_r0:u32 = (R12:u32 $>> low:u32(0x1F:u64))
R0:u32 = tmp_r0:u32
jmp  "pc_0x1040"

addr 0x1040 @asm  "orreq r0, r0, #1"
label pc_0x1040
PC:u32 = 0x1040:u32
TmpV_186:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_186:bool , "L_371" , "pc_0x1044"
label L_371
tmp_r0:u32 = R0:u32 | low:u32(0x1:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x1044"

addr 0x1044 @asm  "bx lr"
label pc_0x1044
PC:u32 = 0x1044:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x1048 @asm  "cmp r1, #0x10000"
label pc_0x1048
PC:u32 = 0x1048:u32
tmp_n_flag:bool = low:bool(low:bool(((R1:u32 + low:u32(0xFFFF0000:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFEFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFEFFFF:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFEFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFEFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R1:u32 + low:u32(0xFFFF0000:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFEFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x104C"

addr 0x104C @asm  "movcs r1, r1, lsr #16"
label pc_0x104C
PC:u32 = 0x104C:u32
TmpV_187:bool = low:bool( C_FLAG:bool)
cjmp TmpV_187:bool , "L_373" , "pc_0x1050"
label L_373
tmp_r1:u32 = (R1:u32 >> low:u32(0x10:u64))
R1:u32 = tmp_r1:u32
jmp  "pc_0x1050"

addr 0x1050 @asm  "movcs r2, #16"
label pc_0x1050
PC:u32 = 0x1050:u32
TmpV_188:bool = low:bool( C_FLAG:bool)
cjmp TmpV_188:bool , "L_375" , "pc_0x1054"
label L_375
tmp_r2:u32 = low:u32(0x10:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x1054"

addr 0x1054 @asm  "movcc r2, #0"
label pc_0x1054
PC:u32 = 0x1054:u32
TmpV_189:bool = low:bool( ~C_FLAG:bool)
cjmp TmpV_189:bool , "L_377" , "pc_0x1058"
label L_377
tmp_r2:u32 = low:u32(0x0:u64)
R2:u32 = tmp_r2:u32
jmp  "pc_0x1058"

addr 0x1058 @asm  "cmp r1, #256"
label pc_0x1058
PC:u32 = 0x1058:u32
tmp_n_flag:bool = low:bool(low:bool(((R1:u32 + low:u32(0xFFFFFF00:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFFFEFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFFFEFF:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFFFEFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFFFEFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R1:u32 + low:u32(0xFFFFFF00:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFFFEFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x105C"

addr 0x105C @asm  "movcs r1, r1, lsr #8"
label pc_0x105C
PC:u32 = 0x105C:u32
TmpV_190:bool = low:bool( C_FLAG:bool)
cjmp TmpV_190:bool , "L_379" , "pc_0x1060"
label L_379
tmp_r1:u32 = (R1:u32 >> low:u32(0x8:u64))
R1:u32 = tmp_r1:u32
jmp  "pc_0x1060"

addr 0x1060 @asm  "addcs r2, r2, #8"
label pc_0x1060
PC:u32 = 0x1060:u32
TmpV_191:bool = low:bool( C_FLAG:bool)
cjmp TmpV_191:bool , "L_381" , "pc_0x1064"
label L_381
tmp_r2:u32 = (R2:u32 + low:u32(0x8:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0x1064"

addr 0x1064 @asm  "cmp r1, #16"
label pc_0x1064
PC:u32 = 0x1064:u32
tmp_n_flag:bool = low:bool(low:bool(((R1:u32 + low:u32(0xFFFFFFF0:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFFFFEF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFFFFEF:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFFFFEF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFFFFEF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R1:u32 + low:u32(0xFFFFFFF0:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFFFFEF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x1068"

addr 0x1068 @asm  "movcs r1, r1, lsr #4"
label pc_0x1068
PC:u32 = 0x1068:u32
TmpV_192:bool = low:bool( C_FLAG:bool)
cjmp TmpV_192:bool , "L_383" , "pc_0x106C"
label L_383
tmp_r1:u32 = (R1:u32 >> low:u32(0x4:u64))
R1:u32 = tmp_r1:u32
jmp  "pc_0x106C"

addr 0x106C @asm  "addcs r2, r2, #4"
label pc_0x106C
PC:u32 = 0x106C:u32
TmpV_193:bool = low:bool( C_FLAG:bool)
cjmp TmpV_193:bool , "L_385" , "pc_0x1070"
label L_385
tmp_r2:u32 = (R2:u32 + low:u32(0x4:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0x1070"

addr 0x1070 @asm  "cmp r1, #4"
label pc_0x1070
PC:u32 = 0x1070:u32
tmp_n_flag:bool = low:bool(low:bool(((R1:u32 + low:u32(0xFFFFFFFC:u64))) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFFFFFB:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFFFFFB:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFFFFFB:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFFFFFB:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool(((R1:u32 + low:u32(0xFFFFFFFC:u64)) == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFFFFFB:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x1074"

addr 0x1074 @asm  "addhi r2, r2, #3"
label pc_0x1074
PC:u32 = 0x1074:u32
TmpV_194:bool = low:bool( C_FLAG:bool & ~Z_FLAG:bool)
cjmp TmpV_194:bool , "L_387" , "pc_0x1078"
label L_387
tmp_r2:u32 = (R2:u32 + low:u32(0x3:u64))
R2:u32 = tmp_r2:u32
jmp  "pc_0x1078"

addr 0x1078 @asm  "addls r2, r2, r1, lsr #1"
label pc_0x1078
PC:u32 = 0x1078:u32
jmp "lift_error"
cjmp TmpV_195:bool , "L_389" , "pc_0x107C"
label L_389
tmp_r2:u32 = (R2:u32 + (R1:u32 >> low:u32(0x1:u64)))
R2:u32 = tmp_r2:u32
jmp  "pc_0x107C"

addr 0x107C @asm  "cmp r12, #0"
label pc_0x107C
PC:u32 = 0x107C:u32
tmp_n_flag:bool = low:bool(low:bool((R12:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R12:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R12:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R12:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R12:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R12:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R12:u32) >> 0x1f:u32 ) & ~(low:bool((R12:u32) >> 0x1f:u32 ) == ((((extend:u64(R12:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x1080"

addr 0x1080 @asm  "mov r0, r3, lsr r2"
label pc_0x1080
PC:u32 = 0x1080:u32
tmp_r0:u32 = (R3:u32 >> low:u32(extend:u64(R2:u32)))
R0:u32 = tmp_r0:u32
jmp  "pc_0x1084"

addr 0x1084 @asm  "rsbmi r0, r0, #0"
label pc_0x1084
PC:u32 = 0x1084:u32
TmpV_196:bool = low:bool( N_FLAG:bool)
cjmp TmpV_196:bool , "L_391" , "pc_0x1088"
label L_391
tmp_r0:u32 =  -R0:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0x1088"

addr 0x1088 @asm  "bx lr"
label pc_0x1088
PC:u32 = 0x1088:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

addr 0x108C @asm  "cmp r0, #0"
label pc_0x108C
PC:u32 = 0x108C:u32
tmp_n_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R0:u32) >> 0x1f:u32 ) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x1090"

addr 0x1090 @asm  "mvngt r0, #0x80000000"
label pc_0x1090
PC:u32 = 0x1090:u32
TmpV_197:bool = low:bool( (N_FLAG:bool == V_FLAG:bool) & ~Z_FLAG:bool)
cjmp TmpV_197:bool , "L_393" , "pc_0x1094"
label L_393
tmp_r0:u32 = low:u32(0x7FFFFFFF:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x1094"

addr 0x1094 @asm  "movlt r0, #0x80000000"
label pc_0x1094
PC:u32 = 0x1094:u32
TmpV_198:bool = low:bool( ~(N_FLAG:bool == V_FLAG:bool))
cjmp TmpV_198:bool , "L_395" , "pc_0x1098"
label L_395
tmp_r0:u32 = low:u32(0x80000000:u64)
R0:u32 = tmp_r0:u32
jmp  "pc_0x1098"

addr 0x1098 @asm  "b +#36"
label pc_0x1098
PC:u32 = 0x1098:u32
jmp  "pc_0x10BC"


addr 0x109C @asm  "cmp r1, #0"
label pc_0x109C
PC:u32 = 0x109C:u32
tmp_n_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ))
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) < 0x100000000:u64 then (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) else ((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64)))
tmp_z_flag:bool = low:bool((R1:u32 == low:u32(0x0:u64)))
tmp_v_flag:bool = low:bool(low:bool((R1:u32) >> 0x1f:u32 ) & ~(low:bool((R1:u32) >> 0x1f:u32 ) == ((((extend:u64(R1:u32) + 0xFFFFFFFF:u64 + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0x10A0"

addr 0x10A0 @asm  "beq -#20"
label pc_0x10A0
PC:u32 = 0x10A0:u32
TmpV_199:bool = low:bool( Z_FLAG:bool)
cjmp TmpV_199:bool , "pc_0x108C" , "pc_0x10A4"

addr 0x10A4 @asm  "push {r0, r1, lr}"
label pc_0x10A4
PC:u32 = 0x10A4:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xFFFFFFF4:u64))
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFFC:u64)) ,e_little]:u32 =LR_SVC:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF8:u64)) ,e_little]:u32 =R1:u32
mem:?u32 = mem:?u32 with [(SP_SVC:u32 + low:u32(0xFFFFFFF4:u64)) ,e_little]:u32 =R0:u32
SP_SVC:u32 = tmp_sp_svc:u32
jmp  "pc_0x10A8"

addr 0x10A8 @asm  "bl -#300"
label pc_0x10A8
PC:u32 = 0x10A8:u32
tmp_lr_svc:u32 = (PC:u32 + low:u32(0x4:u64))
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0xF7C"

addr 0x10AC @asm  "pop {r1, r2, lr}"
label pc_0x10AC
PC:u32 = 0x10AC:u32
tmp_sp_svc:u32 = (SP_SVC:u32 + low:u32(0xC:u64))
tmp_lr_svc:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x8:u64)),e_little]:u32
tmp_r2:u32 = mem:?u32[(SP_SVC:u32 + low:u32(0x4:u64)),e_little]:u32
tmp_r1:u32 = mem:?u32[SP_SVC:u32,e_little]:u32
R1:u32 = tmp_r1:u32
R2:u32 = tmp_r2:u32
SP_SVC:u32 = tmp_sp_svc:u32
LR_SVC:u32 = tmp_lr_svc:u32
jmp  "pc_0x10B0"

addr 0x10B0 @asm  "mul r3, r2, r0"
label pc_0x10B0
PC:u32 = 0x10B0:u32
tmp_r3:u32 = (R2:u32*R0:u32)
R3:u32 = tmp_r3:u32
jmp  "pc_0x10B4"

addr 0x10B4 @asm  "sub r1, r1, r3"
label pc_0x10B4
PC:u32 = 0x10B4:u32
tmp_r1:u32 = (R1:u32 +  -R3:u32)
R1:u32 = tmp_r1:u32
jmp  "pc_0x10B8"

addr 0x10B8 @asm  "bx lr"
label pc_0x10B8
PC:u32 = 0x10B8:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)


addr 0x10BC @asm  "bx lr"
label pc_0x10BC
PC:u32 = 0x10BC:u32
jmp  ( if (LR_SVC:u32 & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*LR_SVC:u32)$/low:u32(0x2:u64)) else LR_SVC:u32)

label lift_error
goal:bool = (~precondition) | false
jmp "end"

label success

mem_rl2:?u32 = mem:?u32;
R0_RL2:u32 = R0:u32
R1_RL2:u32 = R1:u32
R2_RL2:u32 = R2:u32
R3_RL2:u32 = R3:u32
R4_RL2:u32 = R4:u32
R5_RL2:u32 = R5:u32
R6_RL2:u32 = R6:u32
R7_RL2:u32 = R7:u32
R8_RL2:u32 = R8:u32
R9_RL2:u32 = R9:u32
R10_RL2:u32 = R10:u32
R11_RL2:u32 = R11:u32
R12_RL2:u32 = R12:u32
LR_RL2:u32 = LR:u32
SP_RL2:u32 = SP:u32
PC_RL2:u32 = PC:u32
LR_SVC_RL2:u32 = LR_SVC:u32
SP_SVC_RL2:u32 = SP_SVC:u32

N_RL2:bool  = N_FLAG:bool 
C_RL2:bool  = C_FLAG:bool 
Z_RL2:bool  = Z_FLAG:bool 
RV_RL2:bool  = V_FLAG:bool 
Q_RL2:bool  = Q_FLAG:bool 


postcondition:bool = (





















true

)

goal:bool = (~precondition) | postcondition
jmp "end"
label end
