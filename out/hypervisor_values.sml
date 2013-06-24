
(**************************************)
(*           KTH constants values     *)
(**************************************)

(* global symbols *)

val global_minimal_config_add_axiom = new_axiom("global_minimal_config_add_axiom",
   ``global_minimal_config_add = 0x00008244w``);

val global___data_start___add_axiom = new_axiom("global___data_start___add_axiom",
   ``global___data_start___add = 0x000081e4w``);

val global_buffer_out_add_axiom = new_axiom("global_buffer_out_add_axiom",
   ``global_buffer_out_add = 0x00002014w``);

val global_tick_handler_add_axiom = new_axiom("global_tick_handler_add_axiom",
   ``global_tick_handler_add = 0x00002010w``);

val global_gm_interrupt_2_add_axiom = new_axiom("global_gm_interrupt_2_add_axiom",
   ``global_gm_interrupt_2_add = 0x000010d4w``);

val global_gm_interrupt_1_add_axiom = new_axiom("global_gm_interrupt_1_add_axiom",
   ``global_gm_interrupt_1_add = 0x000010acw``);

val global_vm_1_add_axiom = new_axiom("global_vm_1_add_axiom",
   ``global_vm_1_add = 0x00008080w``);

val global_curr_vm_add_axiom = new_axiom("global_curr_vm_add_axiom",
   ``global_curr_vm_add = 0x00008130w``);

val global___bss_end___add_axiom = new_axiom("global___bss_end___add_axiom",
   ``global___bss_end___add = 0x00008000w``);

val global_CSWTCH13_add_axiom = new_axiom("global_CSWTCH13_add_axiom",
   ``global_CSWTCH13_add = 0x00001094w``);

val global_CSWTCH12_add_axiom = new_axiom("global_CSWTCH12_add_axiom",
   ``global_CSWTCH12_add = 0x0000107cw``);

val global_context_stack_add_axiom = new_axiom("global_context_stack_add_axiom",
   ``global_context_stack_add = 0x00008320w``);

val global___bss_start___add_axiom = new_axiom("global___bss_start___add_axiom",
   ``global___bss_start___add = 0x00002000w``);

val global_gm_task_1_add_axiom = new_axiom("global_gm_task_1_add_axiom",
   ``global_gm_task_1_add = 0x000010c0w``);

val global_gm_task_2_add_axiom = new_axiom("global_gm_task_2_add_axiom",
   ``global_gm_task_2_add = 0x000010e8w``);

val global_buffer_in_add_axiom = new_axiom("global_buffer_in_add_axiom",
   ``global_buffer_in_add = 0x00002024w``);

val global_rodatastr11_add_axiom = new_axiom("global_rodatastr11_add_axiom",
   ``global_rodatastr11_add = 0x00000fb0w``);

val global_vm_0_add_axiom = new_axiom("global_vm_0_add_axiom",
   ``global_vm_0_add = 0x00008134w``);

val global_flpt_add_axiom = new_axiom("global_flpt_add_axiom",
   ``global_flpt_add = 0x00004000w``);

val global_family_callback_swi_add_axiom = new_axiom("global_family_callback_swi_add_axiom",
   ``global_family_callback_swi_add = 0x00002008w``);

val global_context_stack_curr_add_axiom = new_axiom("global_context_stack_curr_add_axiom",
   ``global_context_stack_curr_add = 0x0000831cw``);

val global_family_callback_undef_add_axiom = new_axiom("global_family_callback_undef_add_axiom",
   ``global_family_callback_undef_add = 0x0000200cw``);

val global_family_callback_data_abort_add_axiom = new_axiom("global_family_callback_data_abort_add_axiom",
   ``global_family_callback_data_abort_add = 0x00002004w``);

val global_def_context7_add_axiom = new_axiom("global_def_context7_add_axiom",
   ``global_def_context7_add = 0x00008524w``);

val global_def_context6_add_axiom = new_axiom("global_def_context6_add_axiom",
   ``global_def_context6_add = 0x000084d4w``);

val global_def_context5_add_axiom = new_axiom("global_def_context5_add_axiom",
   ``global_def_context5_add = 0x00008484w``);

val global_def_context4_add_axiom = new_axiom("global_def_context4_add_axiom",
   ``global_def_context4_add = 0x00008434w``);

val global_def_context3_add_axiom = new_axiom("global_def_context3_add_axiom",
   ``global_def_context3_add = 0x000083e4w``);

val global_def_context2_add_axiom = new_axiom("global_def_context2_add_axiom",
   ``global_def_context2_add = 0x00008394w``);

val global_def_context1_add_axiom = new_axiom("global_def_context1_add_axiom",
   ``global_def_context1_add = 0x00008344w``);
(* function symbols *)

val f_hypercall_num_error_add_axiom = new_axiom("f_hypercall_num_error_add_axiom",
   ``f_hypercall_num_error_add = 0x0000082cw``);

val f_exception_bottom_add_axiom = new_axiom("f_exception_bottom_add_axiom",
   ``f_exception_bottom_add = 0x00000084w``);

val f_cpu_irq_get_count_add_axiom = new_axiom("f_cpu_irq_get_count_add_axiom",
   ``f_cpu_irq_get_count_add = 0x00000400w``);

val f_cpu_irq_set_handler_add_axiom = new_axiom("f_cpu_irq_set_handler_add_axiom",
   ``f_cpu_irq_set_handler_add = 0x0000043cw``);

val f_hypercall_message_add_axiom = new_axiom("f_hypercall_message_add_axiom",
   ``f_hypercall_message_add = 0x000007ecw``);

val f_mem_mmu_set_enable_add_axiom = new_axiom("f_mem_mmu_set_enable_add_axiom",
   ``f_mem_mmu_set_enable_add = 0x00000bbcw``);

val f_soc_interrupt_init_add_axiom = new_axiom("f_soc_interrupt_init_add_axiom",
   ``f_soc_interrupt_init_add = 0x000004a8w``);

val f_printf_add_axiom = new_axiom("f_printf_add_axiom",
   ``f_printf_add = 0x00000d4cw``);

val f_change_guest_mode_add_axiom = new_axiom("f_change_guest_mode_add_axiom",
   ``f_change_guest_mode_add = 0x000007a8w``);

val f_start_guest_add_axiom = new_axiom("f_start_guest_add_axiom",
   ``f_start_guest_add = 0x00000a24w``);

val f_soc_clocks_init_add_axiom = new_axiom("f_soc_clocks_init_add_axiom",
   ``f_soc_clocks_init_add = 0x000003b0w``);

val f_bss_loop_add_axiom = new_axiom("f_bss_loop_add_axiom",
   ``f_bss_loop_add = 0x00000b40w``);

val f_guests_init_add_axiom = new_axiom("f_guests_init_add_axiom",
   ``f_guests_init_add = 0x00000960w``);

val f_cpu_break_to_debugger_add_axiom = new_axiom("f_cpu_break_to_debugger_add_axiom",
   ``f_cpu_break_to_debugger_add = 0x000002b0w``);

val f_mem_mmu_set_translation_table_add_axiom = new_axiom("f_mem_mmu_set_translation_table_add_axiom",
   ``f_mem_mmu_set_translation_table_add = 0x00000bb4w``);

val f_mem_mmu_tlb_invalidate_one_add_axiom = new_axiom("f_mem_mmu_tlb_invalidate_one_add_axiom",
   ``f_mem_mmu_tlb_invalidate_one_add = 0x00000320w``);

val f_mem_padr_lookup_add_axiom = new_axiom("f_mem_padr_lookup_add_axiom",
   ``f_mem_padr_lookup_add = 0x00000ab0w``);

val f_printf_string_add_axiom = new_axiom("f_printf_string_add_axiom",
   ``f_printf_string_add = 0x00000c30w``);

val f_setup_handlers_add_axiom = new_axiom("f_setup_handlers_add_axiom",
   ``f_setup_handlers_add = 0x00000920w``);

val f_stdio_write_char_add_axiom = new_axiom("f_stdio_write_char_add_axiom",
   ``f_stdio_write_char_add = 0x000005e8w``);

val f_cpu_set_swi_handler_add_axiom = new_axiom("f_cpu_set_swi_handler_add_axiom",
   ``f_cpu_set_swi_handler_add = 0x00000290w``);

val f_stdio_can_write_add_axiom = new_axiom("f_stdio_can_write_add_axiom",
   ``f_stdio_can_write_add = 0x00000620w``);

val f_mem_mmu_tlb_invalidate_all_add_axiom = new_axiom("f_mem_mmu_tlb_invalidate_all_add_axiom",
   ``f_mem_mmu_tlb_invalidate_all_add = 0x000002dcw``);

val f_soc_uart_init_add_axiom = new_axiom("f_soc_uart_init_add_axiom",
   ``f_soc_uart_init_add = 0x00000640w``);

val f_reset_guest_add_axiom = new_axiom("f_reset_guest_add_axiom",
   ``f_reset_guest_add = 0x00000694w``);

val f_timer_tick_start_add_axiom = new_axiom("f_timer_tick_start_add_axiom",
   ``f_timer_tick_start_add = 0x0000051cw``);

val f_printf_bin_add_axiom = new_axiom("f_printf_bin_add_axiom",
   ``f_printf_bin_add = 0x00000d0cw``);

val f_impl_dabort_add_axiom = new_axiom("f_impl_dabort_add_axiom",
   ``f_impl_dabort_add = 0x0000010cw``);

val f_undef_handler_add_axiom = new_axiom("f_undef_handler_add_axiom",
   ``f_undef_handler_add = 0x000007a0w``);

val f_cpu_init_add_axiom = new_axiom("f_cpu_init_add_axiom",
   ``f_cpu_init_add = 0x000002b4w``);

val f_impl_reset_add_axiom = new_axiom("f_impl_reset_add_axiom",
   ``f_impl_reset_add = 0x00000b30w``);

val f_default_handler_add_axiom = new_axiom("f_default_handler_add_axiom",
   ``f_default_handler_add = 0x000003d8w``);

val f_mem_mmu_pid_set_add_axiom = new_axiom("f_mem_mmu_pid_set_add_axiom",
   ``f_mem_mmu_pid_set_add = 0x00000bd4w``);

val f_prog_abort_handler_add_axiom = new_axiom("f_prog_abort_handler_add_axiom",
   ``f_prog_abort_handler_add = 0x00000700w``);

val f___aeabi_idiv0_add_axiom = new_axiom("f___aeabi_idiv0_add_axiom",
   ``f___aeabi_idiv0_add = 0x00000facw``);

val f_printf_int_add_axiom = new_axiom("f_printf_int_add_axiom",
   ``f_printf_int_add = 0x00000c54w``);

val f_mem_cache_set_enable_add_axiom = new_axiom("f_mem_cache_set_enable_add_axiom",
   ``f_mem_cache_set_enable_add = 0x00000360w``);

val f_cpu_context_current_get_add_axiom = new_axiom("f_cpu_context_current_get_add_axiom",
   ``f_cpu_context_current_get_add = 0x00000228w``);

val f_printf_putchar_add_axiom = new_axiom("f_printf_putchar_add_axiom",
   ``f_printf_putchar_add = 0x00000afcw``);

val f_mem_mmu_set_domain_add_axiom = new_axiom("f_mem_mmu_set_domain_add_axiom",
   ``f_mem_mmu_set_domain_add = 0x00000bacw``);

val f_data_abort_handler_add_axiom = new_axiom("f_data_abort_handler_add_axiom",
   ``f_data_abort_handler_add = 0x00000708w``);

val f_cpu_irq_get_current_add_axiom = new_axiom("f_cpu_irq_get_current_add_axiom",
   ``f_cpu_irq_get_current_add = 0x000004a4w``);

val f_tick_handler_stub_add_axiom = new_axiom("f_tick_handler_stub_add_axiom",
   ``f_tick_handler_stub_add = 0x000004ecw``);

val f_soc_timer_init_add_axiom = new_axiom("f_soc_timer_init_add_axiom",
   ``f_soc_timer_init_add = 0x000005bcw``);

val f_cpu_irq_acknowledge_add_axiom = new_axiom("f_cpu_irq_acknowledge_add_axiom",
   ``f_cpu_irq_acknowledge_add = 0x00000460w``);

val f_cpu_irq_set_enable_add_axiom = new_axiom("f_cpu_irq_set_enable_add_axiom",
   ``f_cpu_irq_set_enable_add = 0x00000408w``);

val f_swi_handler_add_axiom = new_axiom("f_swi_handler_add_axiom",
   ``f_swi_handler_add = 0x000006e4w``);

val f_cpu_interrupt_set_add_axiom = new_axiom("f_cpu_interrupt_set_add_axiom",
   ``f_cpu_interrupt_set_add = 0x00000becw``);

val f_timer_tick_stop_add_axiom = new_axiom("f_timer_tick_stop_add_axiom",
   ``f_timer_tick_stop_add = 0x000005a0w``);

val f_cpu_set_undef_handler_add_axiom = new_axiom("f_cpu_set_undef_handler_add_axiom",
   ``f_cpu_set_undef_handler_add = 0x000002a0w``);

val f_terminate_add_axiom = new_axiom("f_terminate_add_axiom",
   ``f_terminate_add = 0x00000b00w``);

val f_cpu_get_type_add_axiom = new_axiom("f_cpu_get_type_add_axiom",
   ``f_cpu_get_type_add = 0x00000270w``);

val f_dcache_clean_add_axiom = new_axiom("f_dcache_clean_add_axiom",
   ``f_dcache_clean_add = 0x00000388w``);

val f_printf_hex_add_axiom = new_axiom("f_printf_hex_add_axiom",
   ``f_printf_hex_add = 0x00000cd4w``);

val f_cpu_context_initial_set_add_axiom = new_axiom("f_cpu_context_initial_set_add_axiom",
   ``f_cpu_context_initial_set_add = 0x00000250w``);

val f___startup_start___add_axiom = new_axiom("f___startup_start___add_axiom",
   ``f___startup_start___add = 0x00000000w``);

val f_cpu_context_depth_get_add_axiom = new_axiom("f_cpu_context_depth_get_add_axiom",
   ``f_cpu_context_depth_get_add = 0x0000025cw``);

val f_cpu_interrupt_user_set_add_axiom = new_axiom("f_cpu_interrupt_user_set_add_axiom",
   ``f_cpu_interrupt_user_set_add = 0x00000c08w``);

val f_mem_cache_invalidate_add_axiom = new_axiom("f_mem_cache_invalidate_add_axiom",
   ``f_mem_cache_invalidate_add = 0x00000378w``);

val f_soc_init_add_axiom = new_axiom("f_soc_init_add_axiom",
   ``f_soc_init_add = 0x000003c0w``);

val f_impl_fiq_add_axiom = new_axiom("f_impl_fiq_add_axiom",
   ``f_impl_fiq_add = 0x000000b0w``);

val f__hang_add_axiom = new_axiom("f__hang_add_axiom",
   ``f__hang_add = 0x00000b9cw``);

val f_impl_swi_add_axiom = new_axiom("f_impl_swi_add_axiom",
   ``f_impl_swi_add = 0x000001b4w``);

val f_hyper_panic_add_axiom = new_axiom("f_hyper_panic_add_axiom",
   ``f_hyper_panic_add = 0x00000830w``);

val f_mem_mmu_pid_get_add_axiom = new_axiom("f_mem_mmu_pid_get_add_axiom",
   ``f_mem_mmu_pid_get_add = 0x00000be0w``);

val f_divsi3_skip_div0_test_add_axiom = new_axiom("f_divsi3_skip_div0_test_add_axiom",
   ``f_divsi3_skip_div0_test_add = 0x00000e6cw``);

val f_irq_handler_add_axiom = new_axiom("f_irq_handler_add_axiom",
   ``f_irq_handler_add = 0x00000710w``);

val f_cpu_context_current_set_add_axiom = new_axiom("f_cpu_context_current_set_add_axiom",
   ``f_cpu_context_current_set_add = 0x0000023cw``);

val f_impl_pabort_add_axiom = new_axiom("f_impl_pabort_add_axiom",
   ``f_impl_pabort_add = 0x000000b4w``);

val f_impl_irq_add_axiom = new_axiom("f_impl_irq_add_axiom",
   ``f_impl_irq_add = 0x00000020w``);

val f___aeabi_idivmod_add_axiom = new_axiom("f___aeabi_idivmod_add_axiom",
   ``f___aeabi_idivmod_add = 0x00000f8cw``);

val f_impl_undef_add_axiom = new_axiom("f_impl_undef_add_axiom",
   ``f_impl_undef_add = 0x00000164w``);

val f_cpu_set_abort_handler_add_axiom = new_axiom("f_cpu_set_abort_handler_add_axiom",
   ``f_cpu_set_abort_handler_add = 0x00000280w``);

val f_stdio_read_char_add_axiom = new_axiom("f_stdio_read_char_add_axiom",
   ``f_stdio_read_char_add = 0x00000618w``);

val f_memory_init_add_axiom = new_axiom("f_memory_init_add_axiom",
   ``f_memory_init_add = 0x00000834w``);

val f_init__add_axiom = new_axiom("f_init__add_axiom",
   ``f_init__add = 0x00000a90w``);

val f___aeabi_idiv_add_axiom = new_axiom("f___aeabi_idiv_add_axiom",
   ``f___aeabi_idiv_add = 0x00000e64w``);

val f_soc_interrupt_set_configuration_add_axiom = new_axiom("f_soc_interrupt_set_configuration_add_axiom",
   ``f_soc_interrupt_set_configuration_add = 0x00000478w``);

val f_stdio_can_read_add_axiom = new_axiom("f_stdio_can_read_add_axiom",
   ``f_stdio_can_read_add = 0x00000638w``);

val f_hypercall_end_interrupt_add_axiom = new_axiom("f_hypercall_end_interrupt_add_axiom",
   ``f_hypercall_end_interrupt_add = 0x0000080cw``);
(* type sizes and offsets *)

val t_hc_mem_domain_len_axiom = new_axiom("t_hc_mem_domain_len_axiom",
   ``t_hc_mem_domain_len = 4w``);

val o_hc_mem_domain__name_axiom = new_axiom("o_hc_mem_domain__name_axiom",
   ``o_hc_mem_domain__name = 0w``);

val t_context_len_axiom = new_axiom("t_context_len_axiom",
   ``t_context_len = 68w``);

val o_context__psr_axiom = new_axiom("o_context__psr_axiom",
   ``o_context__psr = 64w``);

val o_context__pc_axiom = new_axiom("o_context__pc_axiom",
   ``o_context__pc = 60w``);

val o_context__sp_axiom = new_axiom("o_context__sp_axiom",
   ``o_context__sp = 52w``);

val o_context__lr_axiom = new_axiom("o_context__lr_axiom",
   ``o_context__lr = 56w``);

val o_context__reg_axiom = new_axiom("o_context__reg_axiom",
   ``o_context__reg = 0w``);

val t_virtual_machine_len_axiom = new_axiom("t_virtual_machine_len_axiom",
   ``t_virtual_machine_len = 176w``);

val o_virtual_machine__current_mode_state_axiom = new_axiom("o_virtual_machine__current_mode_state_axiom",
   ``o_virtual_machine__current_mode_state = 156w``);

val o_virtual_machine__message_axiom = new_axiom("o_virtual_machine__message_axiom",
   ``o_virtual_machine__message = 168w``);

val o_virtual_machine__next_axiom = new_axiom("o_virtual_machine__next_axiom",
   ``o_virtual_machine__next = 164w``);

val o_virtual_machine__interrupted_mode_axiom = new_axiom("o_virtual_machine__interrupted_mode_axiom",
   ``o_virtual_machine__interrupted_mode = 8w``);

val o_virtual_machine__mode_states_axiom = new_axiom("o_virtual_machine__mode_states_axiom",
   ``o_virtual_machine__mode_states = 12w``);

val o_virtual_machine__b_new_message_axiom = new_axiom("o_virtual_machine__b_new_message_axiom",
   ``o_virtual_machine__b_new_message = 172w``);

val o_virtual_machine__current_guest_mode_axiom = new_axiom("o_virtual_machine__current_guest_mode_axiom",
   ``o_virtual_machine__current_guest_mode = 4w``);

val o_virtual_machine__config_axiom = new_axiom("o_virtual_machine__config_axiom",
   ``o_virtual_machine__config = 160w``);

val o_virtual_machine__id_axiom = new_axiom("o_virtual_machine__id_axiom",
   ``o_virtual_machine__id = 0w``);

val t_hc_config_len_axiom = new_axiom("t_hc_config_len_axiom",
   ``t_hc_config_len = 108w``);

val o_hc_config__mem_domains_axiom = new_axiom("o_hc_config__mem_domains_axiom",
   ``o_hc_config__mem_domains = 12w``);

val o_hc_config__guest_entry_mode_axiom = new_axiom("o_hc_config__guest_entry_mode_axiom",
   ``o_hc_config__guest_entry_mode = 8w``);

val o_hc_config__interrupt_config_axiom = new_axiom("o_hc_config__interrupt_config_axiom",
   ``o_hc_config__interrupt_config = 84w``);

val o_hc_config__guest_entry_point_axiom = new_axiom("o_hc_config__guest_entry_point_axiom",
   ``o_hc_config__guest_entry_point = 0w``);

val o_hc_config__errormode_config_axiom = new_axiom("o_hc_config__errormode_config_axiom",
   ``o_hc_config__errormode_config = 96w``);

val o_hc_config__guest_modes_axiom = new_axiom("o_hc_config__guest_modes_axiom",
   ``o_hc_config__guest_modes = 76w``);

val o_hc_config__guest_entry_sp_axiom = new_axiom("o_hc_config__guest_entry_sp_axiom",
   ``o_hc_config__guest_entry_sp = 4w``);

val t_int_len_axiom = new_axiom("t_int_len_axiom",
   ``t_int_len = 4w``);

val t_hc_errormode_config_len_axiom = new_axiom("t_hc_errormode_config_len_axiom",
   ``t_hc_errormode_config_len = 12w``);

val o_hc_errormode_config__error_handler_axiom = new_axiom("o_hc_errormode_config__error_handler_axiom",
   ``o_hc_errormode_config__error_handler = 8w``);

val o_hc_errormode_config__sp_axiom = new_axiom("o_hc_errormode_config__sp_axiom",
   ``o_hc_errormode_config__sp = 4w``);

val o_hc_errormode_config__error_mode_axiom = new_axiom("o_hc_errormode_config__error_mode_axiom",
   ``o_hc_errormode_config__error_mode = 0w``);

val t_cpu_model_len_axiom = new_axiom("t_cpu_model_len_axiom",
   ``t_cpu_model_len = 1w``);

val t_char_len_axiom = new_axiom("t_char_len_axiom",
   ``t_char_len = 1w``);

val t_hc_interrupt_config_len_axiom = new_axiom("t_hc_interrupt_config_len_axiom",
   ``t_hc_interrupt_config_len = 12w``);

val o_hc_interrupt_config__message_handler_axiom = new_axiom("o_hc_interrupt_config__message_handler_axiom",
   ``o_hc_interrupt_config__message_handler = 8w``);

val o_hc_interrupt_config__interrupt_mode_axiom = new_axiom("o_hc_interrupt_config__interrupt_mode_axiom",
   ``o_hc_interrupt_config__interrupt_mode = 0w``);

val o_hc_interrupt_config__sp_axiom = new_axiom("o_hc_interrupt_config__sp_axiom",
   ``o_hc_interrupt_config__sp = 4w``);

val t_return_value_len_axiom = new_axiom("t_return_value_len_axiom",
   ``t_return_value_len = 1w``);

val t_cpu_type_len_axiom = new_axiom("t_cpu_type_len_axiom",
   ``t_cpu_type_len = 1w``);

val t_uint32_t_len_axiom = new_axiom("t_uint32_t_len_axiom",
   ``t_uint32_t_len = 4w``);

val t_hc_guest_mode_len_axiom = new_axiom("t_hc_guest_mode_len_axiom",
   ``t_hc_guest_mode_len = 20w``);

val o_hc_guest_mode__get_mode_contexts_axiom = new_axiom("o_hc_guest_mode__get_mode_contexts_axiom",
   ``o_hc_guest_mode__get_mode_contexts = 16w``);

val o_hc_guest_mode__domain_ac_axiom = new_axiom("o_hc_guest_mode__domain_ac_axiom",
   ``o_hc_guest_mode__domain_ac = 4w``);

val o_hc_guest_mode__set_mode_contexts_axiom = new_axiom("o_hc_guest_mode__set_mode_contexts_axiom",
   ``o_hc_guest_mode__set_mode_contexts = 12w``);

val o_hc_guest_mode__name_axiom = new_axiom("o_hc_guest_mode__name_axiom",
   ``o_hc_guest_mode__name = 0w``);

val o_hc_guest_mode__capabilities_axiom = new_axiom("o_hc_guest_mode__capabilities_axiom",
   ``o_hc_guest_mode__capabilities = 8w``);

val t_hyper_mode_state_len_axiom = new_axiom("t_hyper_mode_state_len_axiom",
   ``t_hyper_mode_state_len = 72w``);

val o_hyper_mode_state__ctx_axiom = new_axiom("o_hyper_mode_state__ctx_axiom",
   ``o_hyper_mode_state__ctx = 0w``);

val o_hyper_mode_state__mode_config_axiom = new_axiom("o_hyper_mode_state__mode_config_axiom",
   ``o_hyper_mode_state__mode_config = 68w``);

val t_cpu_callback_len_axiom = new_axiom("t_cpu_callback_len_axiom",
   ``t_cpu_callback_len = 4w``);

(* All axioms *)
val hypervisor_constants_axioms = [
global_minimal_config_add_axiom,
global___data_start___add_axiom,
global_buffer_out_add_axiom,
global_tick_handler_add_axiom,
global_gm_interrupt_2_add_axiom,
global_gm_interrupt_1_add_axiom,
global_vm_1_add_axiom,
global_curr_vm_add_axiom,
global___bss_end___add_axiom,
global_CSWTCH13_add_axiom,
global_CSWTCH12_add_axiom,
global_context_stack_add_axiom,
global___bss_start___add_axiom,
global_gm_task_1_add_axiom,
global_gm_task_2_add_axiom,
global_buffer_in_add_axiom,
global_rodatastr11_add_axiom,
global_vm_0_add_axiom,
global_flpt_add_axiom,
global_family_callback_swi_add_axiom,
global_context_stack_curr_add_axiom,
global_family_callback_undef_add_axiom,
global_family_callback_data_abort_add_axiom,
global_def_context7_add_axiom,
global_def_context6_add_axiom,
global_def_context5_add_axiom,
global_def_context4_add_axiom,
global_def_context3_add_axiom,
global_def_context2_add_axiom,
global_def_context1_add_axiom,
f_hypercall_num_error_add_axiom,
f_exception_bottom_add_axiom,
f_cpu_irq_get_count_add_axiom,
f_cpu_irq_set_handler_add_axiom,
f_hypercall_message_add_axiom,
f_mem_mmu_set_enable_add_axiom,
f_soc_interrupt_init_add_axiom,
f_printf_add_axiom,
f_change_guest_mode_add_axiom,
f_start_guest_add_axiom,
f_soc_clocks_init_add_axiom,
f_bss_loop_add_axiom,
f_guests_init_add_axiom,
f_cpu_break_to_debugger_add_axiom,
f_mem_mmu_set_translation_table_add_axiom,
f_mem_mmu_tlb_invalidate_one_add_axiom,
f_mem_padr_lookup_add_axiom,
f_printf_string_add_axiom,
f_setup_handlers_add_axiom,
f_stdio_write_char_add_axiom,
f_cpu_set_swi_handler_add_axiom,
f_stdio_can_write_add_axiom,
f_mem_mmu_tlb_invalidate_all_add_axiom,
f_soc_uart_init_add_axiom,
f_reset_guest_add_axiom,
f_timer_tick_start_add_axiom,
f_printf_bin_add_axiom,
f_impl_dabort_add_axiom,
f_undef_handler_add_axiom,
f_cpu_init_add_axiom,
f_impl_reset_add_axiom,
f_default_handler_add_axiom,
f_mem_mmu_pid_set_add_axiom,
f_prog_abort_handler_add_axiom,
f___aeabi_idiv0_add_axiom,
f_printf_int_add_axiom,
f_mem_cache_set_enable_add_axiom,
f_cpu_context_current_get_add_axiom,
f_printf_putchar_add_axiom,
f_mem_mmu_set_domain_add_axiom,
f_data_abort_handler_add_axiom,
f_cpu_irq_get_current_add_axiom,
f_tick_handler_stub_add_axiom,
f_soc_timer_init_add_axiom,
f_cpu_irq_acknowledge_add_axiom,
f_cpu_irq_set_enable_add_axiom,
f_swi_handler_add_axiom,
f_cpu_interrupt_set_add_axiom,
f_timer_tick_stop_add_axiom,
f_cpu_set_undef_handler_add_axiom,
f_terminate_add_axiom,
f_cpu_get_type_add_axiom,
f_dcache_clean_add_axiom,
f_printf_hex_add_axiom,
f_cpu_context_initial_set_add_axiom,
f___startup_start___add_axiom,
f_cpu_context_depth_get_add_axiom,
f_cpu_interrupt_user_set_add_axiom,
f_mem_cache_invalidate_add_axiom,
f_soc_init_add_axiom,
f_impl_fiq_add_axiom,
f__hang_add_axiom,
f_impl_swi_add_axiom,
f_hyper_panic_add_axiom,
f_mem_mmu_pid_get_add_axiom,
f_divsi3_skip_div0_test_add_axiom,
f_irq_handler_add_axiom,
f_cpu_context_current_set_add_axiom,
f_impl_pabort_add_axiom,
f_impl_irq_add_axiom,
f___aeabi_idivmod_add_axiom,
f_impl_undef_add_axiom,
f_cpu_set_abort_handler_add_axiom,
f_stdio_read_char_add_axiom,
f_memory_init_add_axiom,
f_init__add_axiom,
f___aeabi_idiv_add_axiom,
f_soc_interrupt_set_configuration_add_axiom,
f_stdio_can_read_add_axiom,
f_hypercall_end_interrupt_add_axiom,
t_hc_mem_domain_len_axiom,
o_hc_mem_domain__name_axiom,
t_context_len_axiom,
o_context__psr_axiom,
o_context__pc_axiom,
o_context__sp_axiom,
o_context__lr_axiom,
o_context__reg_axiom,
t_virtual_machine_len_axiom,
o_virtual_machine__current_mode_state_axiom,
o_virtual_machine__message_axiom,
o_virtual_machine__next_axiom,
o_virtual_machine__interrupted_mode_axiom,
o_virtual_machine__mode_states_axiom,
o_virtual_machine__b_new_message_axiom,
o_virtual_machine__current_guest_mode_axiom,
o_virtual_machine__config_axiom,
o_virtual_machine__id_axiom,
t_hc_config_len_axiom,
o_hc_config__mem_domains_axiom,
o_hc_config__guest_entry_mode_axiom,
o_hc_config__interrupt_config_axiom,
o_hc_config__guest_entry_point_axiom,
o_hc_config__errormode_config_axiom,
o_hc_config__guest_modes_axiom,
o_hc_config__guest_entry_sp_axiom,
t_int_len_axiom,
t_hc_errormode_config_len_axiom,
o_hc_errormode_config__error_handler_axiom,
o_hc_errormode_config__sp_axiom,
o_hc_errormode_config__error_mode_axiom,
t_cpu_model_len_axiom,
t_char_len_axiom,
t_hc_interrupt_config_len_axiom,
o_hc_interrupt_config__message_handler_axiom,
o_hc_interrupt_config__interrupt_mode_axiom,
o_hc_interrupt_config__sp_axiom,
t_return_value_len_axiom,
t_cpu_type_len_axiom,
t_uint32_t_len_axiom,
t_hc_guest_mode_len_axiom,
o_hc_guest_mode__get_mode_contexts_axiom,
o_hc_guest_mode__domain_ac_axiom,
o_hc_guest_mode__set_mode_contexts_axiom,
o_hc_guest_mode__name_axiom,
o_hc_guest_mode__capabilities_axiom,
t_hyper_mode_state_len_axiom,
o_hyper_mode_state__ctx_axiom,
o_hyper_mode_state__mode_config_axiom,
t_cpu_callback_len_axiom
];
