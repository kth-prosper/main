
(~((B:u32 >= low:u32(0x0:u64)) & B:u32 < low:u32(0x4000:u64)) | (mem_rl2:?u32[(B:u32 + low:u32(0x4000:u64)),  e_little]:u8 == mem_rl1:?u32[(B:u32 + low:u32(0x4000:u64)),  e_little]:u8)) & 
(~((B:u32 >= low:u32(0x100000:u64)) & B:u32 < low:u32(0x3FFFFC:u64)) | (mem_rl2:?u32[B:u32,  e_little]:u8 == mem_rl1:?u32[B:u32,  e_little]:u8)) & 
(~((B:u32 >= low:u32(0x100000:u64)) & B:u32 < low:u32(0x6FFFFC:u64)) | (mem_rl2:?u32[B:u32,  e_little]:u8 == mem_rl1:?u32[B:u32,  e_little]:u8)) & 
(mem_rl2:?u32[low:u32(0x8298:u64),  e_little]:u32 == low:u32(0x0:u64)) & 
(mem_rl2:?u32[low:u32(0x8304:u64),  e_little]:u32 == low:u32(0x0:u64)) & 
(mem_rl2:?u32[low:u32(0x10A0:u64),  e_little]:u32 == low:u32(0x5:u64)) & 
(mem_rl2:?u32[low:u32(0x10B4:u64),  e_little]:u32 == low:u32(0x5:u64)) & 
(mem_rl2:?u32[low:u32(0x10C8:u64),  e_little]:u32 == low:u32(0x11:u64)) & 
(mem_rl2:?u32[low:u32(0x10DC:u64),  e_little]:u32 == low:u32(0x11:u64)) & 
(mem_rl2:?u32[low:u32(0x831C:u64),  e_little]:u32 == low:u32(0x0:u64)) &

true