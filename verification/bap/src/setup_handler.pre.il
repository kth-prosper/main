my_precondition:bool = 
    (old_SP_SVC:u32 <= (0x100000:u32 - 4:u32)) &
    (old_SP_SVC:u32 >= 0x0f0000:u32)