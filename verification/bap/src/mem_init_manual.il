// 00000978 <memory_init>

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
TmpV_77:bool = low:bool(~E_FLAG:bool & ~Z_FLAG:bool)
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
TmpV_78:bool = low:bool(~E_FLAG:bool & ((~C_FLAG)| Z_FLAG))
cjmp TmpV_78:bool , "L_155" , "pc_0x9B4"
label L_155
tmp_r1:u32 = mem:?u32[(PC:u32 + low:u32(0xA8:u64)),e_little]:u32
R1:u32 = tmp_r1:u32
jmp  "pc_0x9B4"

addr 0x9B4 @asm  "ldrls r2, [r1, r3, lsl #2]"
label pc_0x9B4
PC:u32 = 0x9B4:u32
TmpV_79:bool = low:bool(~E_FLAG:bool & ((~C_FLAG)| Z_FLAG))
cjmp TmpV_79:bool , "L_157" , "pc_0x9B8"
label L_157
tmp_r2:u32 = mem:?u32[(R1:u32 + (R3:u32 << low:u32(0x2:u64))),e_little]:u32
R2:u32 = tmp_r2:u32
jmp  "pc_0x9B8"

addr 0x9B8 @asm  "addls r3, r1, r3, lsl #2"
label pc_0x9B8
PC:u32 = 0x9B8:u32
TmpV_80:bool = low:bool(~E_FLAG:bool & ((~C_FLAG)| Z_FLAG))
cjmp TmpV_80:bool , "L_159" , "pc_0x9BC"
label L_159
tmp_r3:u32 = (R1:u32 + (R3:u32 << low:u32(0x2:u64)))
R3:u32 = tmp_r3:u32
jmp  "pc_0x9BC"

addr 0x9BC @asm  "ldrb r1, [sp, #7]"
label pc_0x9BC
PC:u32 = 0x9BC:u32
tmp_r1:u32 = pad:u32(mem:?u32[(SP_SVC:u32 + low:u32(0x7:u64)) ,e_little]:u8)
R1:u32 = tmp_r1:u32
jmp  "pc_0x9C0"

addr 0x9C0 @asm  "ldrls r3, [r3, #24]"
label pc_0x9C0
PC:u32 = 0x9C0:u32
TmpV_81:bool = low:bool(~E_FLAG:bool & ((~C_FLAG)| Z_FLAG))
cjmp TmpV_81:bool , "L_161" , "pc_0x9C4"
label L_161
tmp_r3:u32 = mem:?u32[(R3:u32 + low:u32(0x18:u64)),e_little]:u32
R3:u32 = tmp_r3:u32
jmp  "pc_0x9C4"

addr 0x9C4 @asm  "movhi r3, #0"
label pc_0x9C4
PC:u32 = 0x9C4:u32
TmpV_82:bool = low:bool(~E_FLAG:bool & C_FLAG:bool & ~Z_FLAG:bool)
cjmp TmpV_82:bool , "L_163" , "pc_0x9C8"
label L_163
tmp_r3:u32 = low:u32(0x0:u64)
R3:u32 = tmp_r3:u32
jmp  "pc_0x9C8"

addr 0x9C8 @asm  "movhi r2, #2"
label pc_0x9C8
PC:u32 = 0x9C8:u32
TmpV_83:bool = low:bool(~E_FLAG:bool & C_FLAG:bool & ~Z_FLAG:bool)
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
TmpV_84:bool = low:bool(~E_FLAG:bool & ~Z_FLAG:bool)
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
TmpV_85:bool = low:bool(~E_FLAG:bool & Z_FLAG:bool)
cjmp TmpV_85:bool , "L_169" , "pc_0x9E0"
label L_169
tmp_r4:u32 = R6:u32 | low:u32(0x12:u64)
R4:u32 = tmp_r4:u32
jmp  "pc_0x9E0"

addr 0x9E0 @asm  "orreq r4, r4, r2, lsl #5"
label pc_0x9E0
PC:u32 = 0x9E0:u32
TmpV_86:bool = low:bool(~E_FLAG:bool & Z_FLAG:bool)
cjmp TmpV_86:bool , "L_171" , "pc_0x9E4"
label L_171
tmp_r4:u32 = R4:u32 | (R2:u32 << low:u32(0x5:u64))
R4:u32 = tmp_r4:u32
jmp  "pc_0x9E4"

addr 0x9E4 @asm  "orreq r4, r4, r3, lsl #10"
label pc_0x9E4
PC:u32 = 0x9E4:u32
TmpV_87:bool = low:bool(~E_FLAG:bool & Z_FLAG:bool)
cjmp TmpV_87:bool , "L_173" , "pc_0x9E8"
label L_173
tmp_r4:u32 = R4:u32 | (R3:u32 << low:u32(0xA:u64))
R4:u32 = tmp_r4:u32
jmp  "pc_0x9E8"

addr 0x9E8 @asm  "beq +#52"
label pc_0x9E8
PC:u32 = 0x9E8:u32
TmpV_88:bool = low:bool(~E_FLAG:bool & Z_FLAG:bool)
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
TmpV_89:bool = low:bool(~E_FLAG:bool & ~Z_FLAG:bool)
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
TmpV_90:bool = low:bool(~E_FLAG:bool & ~Z_FLAG:bool)
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
TmpV_91:bool = low:bool(~E_FLAG:bool & Z_FLAG:bool)
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
TmpV_92:bool = low:bool(~E_FLAG:bool & ~Z_FLAG:bool)
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
TmpV_93:bool = low:bool(~E_FLAG:bool & ~Z_FLAG:bool)
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
jmp  ( if (UNSUPPORTED & (0x1:u32 << (low:u32(0x0:u64)))) >> low:u32(0x0:u64) then ((low:u32(0x2:u64)*UNSUPPORTED)$/low:u32(0x2:u64)) else UNSUPPORTED)

addr 0xA54 @asm  "strdeq r3, r4, [r0], -r12"
label pc_0xA54

//Failed to lift
jmp "lift_error"

addr 0xA58 @asm  "andeq r1, r0, r12, ror #6"
label pc_0xA58
PC:u32 = 0xA58:u32
TmpV_94:bool = low:bool(~E_FLAG:bool & Z_FLAG:bool)
cjmp TmpV_94:bool , "L_187" , "pc_0xA5C"
label L_187
tmp_r1:u32 = (R0:u32 & UNSUPPORTED)
R1:u32 = tmp_r1:u32
jmp  "pc_0xA5C"

addr 0xA5C @asm  "ldrbpl r5, [r5, #-1365]"
label pc_0xA5C
PC:u32 = 0xA5C:u32
TmpV_95:bool = low:bool(~E_FLAG:bool & ~N_FLAG:bool)
cjmp TmpV_95:bool , "L_189" , "pc_0xA60"
label L_189
r5:u32 = pad:u32(mem:?u32[(R5:u32 + low:u32(0xFFFFFAAB:u64)) ,e_little]:u8)
R5:u32 = tmp_r5:u32
jmp  "pc_0xA60"

addr 0xA60 @asm  "andeq r4, r0, r0"
label pc_0xA60
PC:u32 = 0xA60:u32
TmpV_96:bool = low:bool(~E_FLAG:bool & Z_FLAG:bool)
cjmp TmpV_96:bool , "L_191" , "pc_0xA64"
label L_191
tmp_r4:u32 = R0:u32
R4:u32 = tmp_r4:u32
jmp  "pc_0xA64"
