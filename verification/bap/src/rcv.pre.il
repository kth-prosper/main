my_precondition:bool = 
  ((old_vm0_active &
    (old_mem[$global_vm_1_add+$o_virtual_machine:b_new_message, e_little]:u32 <> 0x0:u32
  ) &
    (old_mem[$global_vm_1_add+$o_virtual_machine:current_guest_mode, e_little]:u32 == 0x1:u32
 )  
 )|
  (old_vm1_active &
    (old_mem[$global_vm_0_add+$o_virtual_machine:b_new_message, e_little]:u32 <> 0x0:u32
    )
    &
   (old_mem[$global_vm_0_add+$o_virtual_machine:current_guest_mode, e_little]:u32 == 0x1:u32
   ) 
  ))
