postcondition:bool = (
  (
   (free_addr:u32 < ($global_tick_handler_add+4:u32)) &
   (free_addr:u32 >= ($global_tick_handler_add))
  ) |
  (
   (free_addr:u32 < ($global_family_callback_undef_add+4:u32)) &
   (free_addr:u32 >= ($global_family_callback_undef_add))
  ) |
  (
   (free_addr:u32 < ($global_family_callback_swi_add+4:u32)) &
   (free_addr:u32 >= ($global_family_callback_swi_add))
  ) |
  (
   (free_addr:u32 < ($global_family_callback_data_abort_add+4:u32)) &
   (free_addr:u32 >= ($global_family_callback_data_abort_add))
  ) |
  (
    (free_addr:u32 < ($global___bss_start___add+4:u32)) &
    (free_addr:u32 >= ($global___bss_start___add))
  ) |
  (
    (free_addr:u32 < (old_SP_SVC:u32 -4:u32+4:u32)) &
    (free_addr:u32 >= (old_SP_SVC:u32 -8:u32))
  ) |
  (
    free_addr:u32 >= 0xfffe0040:u32
  )
  |
  old_mem[free_addr:u32,e_little]:u8 == mem[free_addr:u32,e_little]:u8
) &
(
  mem[$global_family_callback_swi_add,e_little]:u32 == $f_swi_handler_add &
  mem[$global_tick_handler_add,e_little]:u32 == $f_irq_handler_add
) &
(
  R5 == old_R5 &
  R6 == old_R6 &
  R7 == old_R7 &
  R8 == old_R8 &
  R9 == old_R9 &
  R10 == old_R10 &
  R11 == old_R11 &
  R12 == old_R12 &
  SP_SVC == old_SP_SVC &
  true
)
