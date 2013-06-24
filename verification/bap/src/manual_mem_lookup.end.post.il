#set look_up_post=[[
  (~(param:u32 >= 0:u32 & param:u32 <= 0xff:u32) |
   (R0 == $global___data_start___add)) &
  (~(param:u32 >= 0x100:u32 & param:u32 <= 0x1ff:u32) |
   (R0 == $global___data_start___add + (1:u32 * 4:u32*4:u32))) &
  (~(param:u32 >= 0x200:u32 & param:u32 <= 0x2ff:u32) |
   (R0 == $global___data_start___add + (2:u32 * 4:u32*4:u32)))
]]

