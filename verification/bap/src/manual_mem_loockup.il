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
TmpV_110:bool = low:bool(~E_FLAG:bool & Z_FLAG:bool)
cjmp TmpV_110:bool , "lbl_loop_nocontinue3" , "pc_0xBDC"

label lbl_loop_nocontinue3
to_loop:bool = false
jmp "lbl_loop_end"

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
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + (extend:u64( ~R2:u32) & 0xffffffff:u64) + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + (extend:u64( ~R2:u32) & 0xffffffff:u64) + 0x1:u64) else ((extend:u64(R0:u32) + (extend:u64( ~R2:u32) & 0xffffffff:u64) + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + (extend:u64( ~R2:u32) & 0xffffffff:u64) + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == R2:u32))
tmp_v_flag:bool = low:bool((low:bool((R0:u32) >> 0x1f:u32 ) == low:bool(( ~R2:u32) >> 0x1f:u32 )) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + (extend:u64( ~R2:u32) & 0xffffffff:u64) + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xBE4"

addr 0xBE4 @asm  "bcc +#20"
label pc_0xBE4
PC:u32 = 0xBE4:u32
TmpV_111:bool = low:bool(~E_FLAG:bool & ~C_FLAG:bool)
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
tmp_c_flag:bool = low:bool(~(( if (extend:u64(R0:u32) + (extend:u64( ~R2:u32) & 0xffffffff:u64) + 0x1:u64) < 0x100000000:u64 then (extend:u64(R0:u32) + (extend:u64( ~R2:u32) & 0xffffffff:u64) + 0x1:u64) else ((extend:u64(R0:u32) + (extend:u64( ~R2:u32) & 0xffffffff:u64) + 0x1:u64) % 0x100000000:u64)) == (extend:u64(R0:u32) + (extend:u64( ~R2:u32) & 0xffffffff:u64) + 0x1:u64)))
tmp_z_flag:bool = low:bool((R0:u32 == R2:u32))
tmp_v_flag:bool = low:bool((low:bool((R0:u32) >> 0x1f:u32 ) == low:bool(( ~R2:u32) >> 0x1f:u32 )) & ~(low:bool((R0:u32) >> 0x1f:u32 ) == ((((extend:u64(R0:u32) + (extend:u64( ~R2:u32) & 0xffffffff:u64) + 0x1:u64) / (0x1:u64<< 0x1F:u64)) % 0x2:u64) ==0x1:u64)))
N_FLAG:bool = tmp_n_flag:bool
C_FLAG:bool = tmp_c_flag:bool
Z_FLAG:bool = tmp_z_flag:bool
V_FLAG:bool = tmp_v_flag:bool
jmp  "pc_0xBF4"

addr 0xBF4 @asm  "bls +#24"
label pc_0xBF4
PC:u32 = 0xBF4:u32
TmpV_112:bool = low:bool(~E_FLAG:bool & ((~ C_FLAG) | Z_FLAG))
cjmp TmpV_112:bool , "lbl_loop_nocontinue2" , "pc_0xBF8"

label lbl_loop_nocontinue2
to_loop:bool = false
jmp "lbl_loop_end"

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
TmpV_113:bool = low:bool(~E_FLAG:bool & Z_FLAG:bool)
cjmp TmpV_113:bool , "L_225" , "pc_0xC04"
label L_225
tmp_r3:u32 = (R3:u32 + low:u32(0x10:u64))
R3:u32 = tmp_r3:u32
jmp  "pc_0xC04"

addr 0xC04 @asm  "beq -#48"
label pc_0xC04
PC:u32 = 0xC04:u32
TmpV_114:bool = low:bool(~E_FLAG:bool & Z_FLAG:bool)
cjmp TmpV_114:bool , "lbl_loop_continue1" , "pc_0xC08"

label lbl_loop_continue1
to_loop:bool = true
jmp "lbl_loop_end"

addr 0xC08 @asm  "mov r3, #0"
label pc_0xC08
PC:u32 = 0xC08:u32
tmp_r3:u32 = low:u32(0x0:u64)
R3:u32 = tmp_r3:u32
to_loop:bool = false
jmp  "lbl_loop_end"

label lbl_loop_end
cjmp to_loop, "pc_0xBD4", "lbl_loop_exit"

label lbl_loop_exit

addr 0xC0C @asm  "mov r0, r3"
label pc_0xC0C
PC:u32 = 0xC0C:u32
tmp_r0:u32 = R3:u32
R0:u32 = tmp_r0:u32
jmp  "pc_0xC10"

addr 0xC10 @asm  "mov pc, lr"
label pc_0xC10
PC:u32 = 0xC10:u32
jmp  "end"

addr 0xC14 @asm  "andeq r8, r0, r4, ror #3"
label pc_0xC14
PC:u32 = 0xC14:u32
TmpV_115:bool = low:bool(~E_FLAG:bool & Z_FLAG:bool)
cjmp TmpV_115:bool , "L_229" , "pc_0xC18"
label L_229
tmp_r8:u32 = (R0:u32 & UNSUPPORTED:u32)
R8:u32 = tmp_r8:u32
jmp  "pc_0xC18"
