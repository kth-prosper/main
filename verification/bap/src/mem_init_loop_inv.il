#set ptcnd=[[
(
  (~(add < R5)) |
   (
      ((~(add >= 0:u32 & add <= 0xff:u32)) |
        (((mem[$global_flpt_add + 4:u32*add:u32, e_little]:u32 >> 5:u32) & 0xf:u32) == 0:u32)
      ) &
      ((~(add >= 0x100:u32 & add <= 0x1ff:u32)) |
        (((mem[$global_flpt_add + 4:u32*add:u32, e_little]:u32 >> 5:u32) & 0xf:u32) == 1:u32)
      ) &
      ((~(add >= 0x200:u32 & add <= 0x2ff:u32)) |
        (((mem[$global_flpt_add + 4:u32*add:u32, e_little]:u32 >> 5:u32) & 0xf:u32) == 2:u32)
      )
   )
)
]]
