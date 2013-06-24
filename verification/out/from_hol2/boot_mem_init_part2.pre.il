(R5_RL1:u32 >= low:u32(0x0:u64)) & 
R5_RL1:u32 < low:u32(0x1000:u64) & 
(R7_RL1:u32 == (low:u32(0x3FFC:u64) + (low:u32(0x4:u64)*R5_RL1:u32))) & 
(mem_rl1:?u32[low:u32(0x8298:u64),  e_little]:u32 == low:u32(0x0:u64)) & 
(mem_rl1:?u32[low:u32(0x8304:u64),  e_little]:u32 == low:u32(0x0:u64)) & 
(mem_rl1:?u32[low:u32(0x10A0:u64),  e_little]:u32 == low:u32(0x5:u64)) & 
(mem_rl1:?u32[low:u32(0x10B4:u64),  e_little]:u32 == low:u32(0x5:u64)) & 
(mem_rl1:?u32[low:u32(0x10C8:u64),  e_little]:u32 == low:u32(0x11:u64)) & 
(mem_rl1:?u32[low:u32(0x10DC:u64),  e_little]:u32 == low:u32(0x11:u64)) & 
(mem_rl1:?u32[low:u32(0x831C:u64),  e_little]:u32 == low:u32(0x0:u64))