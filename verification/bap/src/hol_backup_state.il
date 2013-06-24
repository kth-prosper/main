// Backup of the state before execution
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

int_count:u64 = 0:u64
