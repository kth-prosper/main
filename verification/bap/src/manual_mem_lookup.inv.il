#set loop_pre_cells = [[
    // for all x < idx_limit => not M[R3]
    // x = 0
    (
      (~($global___data_start___add+0:u32 < idx_limit)) |
      (
         mem[$global___data_start___add+0:u32+(0:u32 * 4:u32*4:u32), e_little]:u32 > param:u32 |
      	 (mem[$global___data_start___add+0:u32+(0:u32 * 4:u32*4:u32), e_little]:u32
	  + mem[$global___data_start___add+4:u32+(0:u32 * 4:u32*4:u32), e_little]:u32
	  ) < param:u32
      )
    ) &
    (
      (~($global___data_start___add+(1:u32 * 4:u32*4:u32) < idx_limit)) |
      (
         mem[$global___data_start___add+0:u32+(1:u32 * 4:u32*4:u32), e_little]:u32 > param:u32 |
      	 (mem[$global___data_start___add+0:u32+(1:u32 * 4:u32*4:u32), e_little]:u32
	  + mem[$global___data_start___add+4:u32+(1:u32 * 4:u32*4:u32), e_little]:u32
	  ) < param:u32
      )
    ) &
    (
      (~($global___data_start___add+(2:u32 * 4:u32*4:u32) < idx_limit)) |
      (
         mem[$global___data_start___add+0:u32+(2:u32 * 4:u32*4:u32), e_little]:u32 > param:u32 |
      	 (mem[$global___data_start___add+0:u32+(2:u32 * 4:u32*4:u32), e_little]:u32
	  + mem[$global___data_start___add+4:u32+(2:u32 * 4:u32*4:u32), e_little]:u32
	  ) < param:u32
      )
    )
]]

#set r3_range = [[
(
    (R3 - $global___data_start___add) $>= 0:u32 &
    ((R3 - $global___data_start___add) % (4:u32*4:u32)) == 0:u32 &
    ((R3 - $global___data_start___add) $<= (2:u32 * 4:u32*4:u32))
)
]]

#set mem_conf = [[
  (mem[$global___data_start___add+0:u32+(0:u32 * 4:u32*4:u32), e_little]:u32 <= (0xFFFFFFFF:u32 >> low:u32(0xC:u64))) &
  (mem[$global___data_start___add+4:u32+(0:u32 * 4:u32*4:u32), e_little]:u32 <= (0xFFFFFFFF:u32 >> low:u32(0xC:u64))) &
  (mem[$global___data_start___add+0:u32+(1:u32 * 4:u32*4:u32), e_little]:u32 <= (0xFFFFFFFF:u32 >> low:u32(0xC:u64))) &
  (mem[$global___data_start___add+4:u32+(1:u32 * 4:u32*4:u32), e_little]:u32 <= (0xFFFFFFFF:u32 >> low:u32(0xC:u64))) &
  (mem[$global___data_start___add+0:u32+(2:u32 * 4:u32*4:u32), e_little]:u32 <= (0xFFFFFFFF:u32 >> low:u32(0xC:u64))) &
  (mem[$global___data_start___add+4:u32+(2:u32 * 4:u32*4:u32), e_little]:u32 <= (0xFFFFFFFF:u32 >> low:u32(0xC:u64))) &

  mem[$global___data_start___add+0xC:u32+(0:u32 * 4:u32*4:u32), e_little]:u32 == 0:u32 &
  mem[$global___data_start___add+0xC:u32+(1:u32 * 4:u32*4:u32), e_little]:u32 == 0:u32 &
  mem[$global___data_start___add+0xC:u32+(2:u32 * 4:u32*4:u32), e_little]:u32 == 1:u32
]]

#set loop_inv = [[
  (param:u32 <= (0xFFFFFFFF:u32 >> low:u32(0xC:u64))) &
  $mem_conf &
  ((~to_loop:bool) | (
    $r3_range
    &
    let idx_limit:u32 := R3 in ($loop_pre_cells)
  )) &

  // Loop exit
  ((~~to_loop:bool) | (
    // success
    ($r3_range &
      (
         mem[R3, e_little]:u32 <= param:u32 &
      	 (mem[R3, e_little]:u32 +
	  mem[R3+4:u32, e_little]:u32
	  ) >= param:u32
      )
    ) |
    // fail
    (R3 == 0:u32 &
    let idx_limit:u32 := $global___data_start___add+(3:u32 * 4:u32*4:u32) in ($loop_pre_cells)
    )
  ))
]]