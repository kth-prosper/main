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
PC_RL1:u32 = PC:u32

LR_UND_RL1:u32 = LR_SVC:u32


N_CURR__RL1:bool  = N_FLAG:bool 
C_CURR__RL1:bool  = C_FLAG:bool 
Z_CURR__RL1:bool  = Z_FLAG:bool 
RV_CURR__RL1:bool  = V_FLAG:bool 
Q_CURR__RL1:bool  = Q_FLAG:bool 
J_CURR__RL1:bool = J_FLAG:bool
E_CURR__RL1:bool = E_FLAG:bool
A_CURR__RL1:bool = A_FLAG:bool
I_CURR__RL1:bool = I_FLAG:bool
F_CURR__RL1:bool = F_FLAG:bool
T_CURR__RL1:bool = T_FLAG:bool

M_CURR__RL1:u8 = M_FLAG:u8


N_UND__RL1:bool  = SVC_N_FLAG:bool 
C_UND__RL1:bool  = SVC_C_FLAG:bool 
Z_UND__RL1:bool  = SVC_Z_FLAG:bool 
RV_UND__RL1:bool  = SVC_V_FLAG:bool 
Q_UND__RL1:bool  = SVC_Q_FLAG:bool 
J_UND__RL1:bool = SVC_J_FLAG:bool
E_UND__RL1:bool = SVC_E_FLAG:bool
A_UND__RL1:bool = SVC_A_FLAG:bool
I_UND__RL1:bool = SVC_I_FLAG:bool
F_UND__RL1:bool = SVC_F_FLAG:bool
T_UND__RL1:bool = SVC_T_FLAG:bool

M_UND__RL1:u8 = SVC_M_FLAG:u8

old_CR0:u32 = CR0:u32
old_CR3:u32 = CR3:u32

COP_EE:bool = COP_EE_RL1:bool
COP_V:bool = COP_V_RL1:bool
CR0:u32 = COP_C0_RL1:u32
CR1:u32 = COP_C1_RL1:u32
CR2:u32 = COP_C2_RL1:u32
CR3:u32 = COP_C3_RL1:u32

int_count:u64 = 0:u64
