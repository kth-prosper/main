
(**************************************)
(*           KTH constants            *)
(**************************************)

(* global symbol locations *)
new_constant ("global_minimal_config_add", ``:word32``);
new_constant ("global___data_start___add", ``:word32``);
new_constant ("global_eade_add", ``:word32``);
new_constant ("global_buffer_out_add", ``:word32``);
new_constant ("global_tick_handler_add", ``:word32``);
new_constant ("global_gm_interrupt_2_add", ``:word32``);
new_constant ("global_gm_interrupt_1_add", ``:word32``);
new_constant ("global_vm_1_add", ``:word32``);
new_constant ("global_curr_vm_add", ``:word32``);
new_constant ("global___bss_end___add", ``:word32``);
new_constant ("global_CSWTCH13_add", ``:word32``);
new_constant ("global_CSWTCH12_add", ``:word32``);
new_constant ("global_context_stack_add", ``:word32``);
new_constant ("global___bss_start___add", ``:word32``);
new_constant ("global_gm_task_1_add", ``:word32``);
new_constant ("global_gm_task_2_add", ``:word32``);
new_constant ("global_buffer_in_add", ``:word32``);
new_constant ("global_rodatastr11_add", ``:word32``);
new_constant ("global_ABL_add", ``:word32``);
new_constant ("global_vm_0_add", ``:word32``);
new_constant ("global_flpt_add", ``:word32``);
new_constant ("global_family_callback_swi_add", ``:word32``);
new_constant ("global_context_stack_curr_add", ``:word32``);
new_constant ("global_family_callback_undef_add", ``:word32``);
new_constant ("global_family_callback_data_abort_add", ``:word32``);
new_constant ("global_def_context7_add", ``:word32``);
new_constant ("global_def_context6_add", ``:word32``);
new_constant ("global_def_context5_add", ``:word32``);
new_constant ("global_def_context4_add", ``:word32``);
new_constant ("global_def_context3_add", ``:word32``);
new_constant ("global_def_context2_add", ``:word32``);
new_constant ("global_def_context1_add", ``:word32``);
(* function symbols *)
new_constant ("f_hypercall_num_error_add", ``:word32``);
new_constant ("f_exception_bottom_add", ``:word32``);
new_constant ("f_cpu_irq_get_count_add", ``:word32``);
new_constant ("f_cpu_irq_set_handler_add", ``:word32``);
new_constant ("f_hypercall_message_add", ``:word32``);
new_constant ("f_mem_mmu_set_enable_add", ``:word32``);
new_constant ("f_soc_interrupt_init_add", ``:word32``);
new_constant ("f_printf_add", ``:word32``);
new_constant ("f_change_guest_mode_add", ``:word32``);
new_constant ("f_start_guest_add", ``:word32``);
new_constant ("f_soc_clocks_init_add", ``:word32``);
new_constant ("f_bss_loop_add", ``:word32``);
new_constant ("f_guests_init_add", ``:word32``);
new_constant ("f_cpu_break_to_debugger_add", ``:word32``);
new_constant ("f_mem_mmu_set_translation_table_add", ``:word32``);
new_constant ("f_mem_mmu_tlb_invalidate_one_add", ``:word32``);
new_constant ("f_mem_padr_lookup_add", ``:word32``);
new_constant ("f_printf_string_add", ``:word32``);
new_constant ("f_setup_handlers_add", ``:word32``);
new_constant ("f_stdio_write_char_add", ``:word32``);
new_constant ("f_cpu_set_swi_handler_add", ``:word32``);
new_constant ("f_stdio_can_write_add", ``:word32``);
new_constant ("f_mem_mmu_tlb_invalidate_all_add", ``:word32``);
new_constant ("f_soc_uart_init_add", ``:word32``);
new_constant ("f_reset_guest_add", ``:word32``);
new_constant ("f_timer_tick_start_add", ``:word32``);
new_constant ("f_printf_bin_add", ``:word32``);
new_constant ("f_impl_dabort_add", ``:word32``);
new_constant ("f_undef_handler_add", ``:word32``);
new_constant ("f_cpu_init_add", ``:word32``);
new_constant ("f_impl_reset_add", ``:word32``);
new_constant ("f_default_handler_add", ``:word32``);
new_constant ("f_mem_mmu_pid_set_add", ``:word32``);
new_constant ("f_prog_abort_handler_add", ``:word32``);
new_constant ("f___aeabi_idiv0_add", ``:word32``);
new_constant ("f_printf_int_add", ``:word32``);
new_constant ("f_mem_cache_set_enable_add", ``:word32``);
new_constant ("f_cpu_context_current_get_add", ``:word32``);
new_constant ("f_printf_putchar_add", ``:word32``);
new_constant ("f_mem_mmu_set_domain_add", ``:word32``);
new_constant ("f_data_abort_handler_add", ``:word32``);
new_constant ("f_cpu_irq_get_current_add", ``:word32``);
new_constant ("f_tick_handler_stub_add", ``:word32``);
new_constant ("f_soc_timer_init_add", ``:word32``);
new_constant ("f_cpu_irq_acknowledge_add", ``:word32``);
new_constant ("f_cpu_irq_set_enable_add", ``:word32``);
new_constant ("f_swi_handler_add", ``:word32``);
new_constant ("f_cpu_interrupt_set_add", ``:word32``);
new_constant ("f_timer_tick_stop_add", ``:word32``);
new_constant ("f_cpu_set_undef_handler_add", ``:word32``);
new_constant ("f_terminate_add", ``:word32``);
new_constant ("f_cpu_get_type_add", ``:word32``);
new_constant ("f_dcache_clean_add", ``:word32``);
new_constant ("f_printf_hex_add", ``:word32``);
new_constant ("f_cpu_context_initial_set_add", ``:word32``);
new_constant ("f___startup_start___add", ``:word32``);
new_constant ("f_cpu_context_depth_get_add", ``:word32``);
new_constant ("f_cpu_interrupt_user_set_add", ``:word32``);
new_constant ("f_mem_cache_invalidate_add", ``:word32``);
new_constant ("f_soc_init_add", ``:word32``);
new_constant ("f_impl_fiq_add", ``:word32``);
new_constant ("f__hang_add", ``:word32``);
new_constant ("f_impl_swi_add", ``:word32``);
new_constant ("f_hyper_panic_add", ``:word32``);
new_constant ("f_mem_mmu_pid_get_add", ``:word32``);
new_constant ("f_divsi3_skip_div0_test_add", ``:word32``);
new_constant ("f_irq_handler_add", ``:word32``);
new_constant ("f_cpu_context_current_set_add", ``:word32``);
new_constant ("f_impl_pabort_add", ``:word32``);
new_constant ("f_impl_irq_add", ``:word32``);
new_constant ("f___aeabi_idivmod_add", ``:word32``);
new_constant ("f_impl_undef_add", ``:word32``);
new_constant ("f_cpu_set_abort_handler_add", ``:word32``);
new_constant ("f_stdio_read_char_add", ``:word32``);
new_constant ("f_memory_init_add", ``:word32``);
new_constant ("f_init__add", ``:word32``);
new_constant ("f___aeabi_idiv_add", ``:word32``);
new_constant ("f_soc_interrupt_set_configuration_add", ``:word32``);
new_constant ("f_stdio_can_read_add", ``:word32``);
new_constant ("f_hypercall_end_interrupt_add", ``:word32``);
(* type sizes and offsets *)
new_constant ("t_hc_mem_domain_len", ``:word32``);
new_constant ("o_hc_mem_domain__name", ``:word32``);
new_constant ("t_context_len", ``:word32``);
new_constant ("o_context__psr", ``:word32``);
new_constant ("o_context__pc", ``:word32``);
new_constant ("o_context__sp", ``:word32``);
new_constant ("o_context__lr", ``:word32``);
new_constant ("o_context__reg", ``:word32``);
new_constant ("t_virtual_machine_len", ``:word32``);
new_constant ("o_virtual_machine__current_mode_state", ``:word32``);
new_constant ("o_virtual_machine__message", ``:word32``);
new_constant ("o_virtual_machine__next", ``:word32``);
new_constant ("o_virtual_machine__interrupted_mode", ``:word32``);
new_constant ("o_virtual_machine__mode_states", ``:word32``);
new_constant ("o_virtual_machine__b_new_message", ``:word32``);
new_constant ("o_virtual_machine__current_guest_mode", ``:word32``);
new_constant ("o_virtual_machine__config", ``:word32``);
new_constant ("o_virtual_machine__id", ``:word32``);
new_constant ("t_hc_config_len", ``:word32``);
new_constant ("o_hc_config__mem_domains", ``:word32``);
new_constant ("o_hc_config__guest_entry_mode", ``:word32``);
new_constant ("o_hc_config__interrupt_config", ``:word32``);
new_constant ("o_hc_config__guest_entry_point", ``:word32``);
new_constant ("o_hc_config__errormode_config", ``:word32``);
new_constant ("o_hc_config__guest_modes", ``:word32``);
new_constant ("o_hc_config__guest_entry_sp", ``:word32``);
new_constant ("t_int_len", ``:word32``);
new_constant ("t_hc_errormode_config_len", ``:word32``);
new_constant ("o_hc_errormode_config__error_handler", ``:word32``);
new_constant ("o_hc_errormode_config__sp", ``:word32``);
new_constant ("o_hc_errormode_config__error_mode", ``:word32``);
new_constant ("t_cpu_model_len", ``:word32``);
new_constant ("t_char_len", ``:word32``);
new_constant ("t_hc_interrupt_config_len", ``:word32``);
new_constant ("o_hc_interrupt_config__message_handler", ``:word32``);
new_constant ("o_hc_interrupt_config__interrupt_mode", ``:word32``);
new_constant ("o_hc_interrupt_config__sp", ``:word32``);
new_constant ("t_return_value_len", ``:word32``);
new_constant ("t_cpu_type_len", ``:word32``);
new_constant ("t_uint32_t_len", ``:word32``);
new_constant ("t_hc_guest_mode_len", ``:word32``);
new_constant ("o_hc_guest_mode__get_mode_contexts", ``:word32``);
new_constant ("o_hc_guest_mode__domain_ac", ``:word32``);
new_constant ("o_hc_guest_mode__set_mode_contexts", ``:word32``);
new_constant ("o_hc_guest_mode__name", ``:word32``);
new_constant ("o_hc_guest_mode__capabilities", ``:word32``);
new_constant ("t_hyper_mode_state_len", ``:word32``);
new_constant ("o_hyper_mode_state__ctx", ``:word32``);
new_constant ("o_hyper_mode_state__mode_config", ``:word32``);
new_constant ("t_cpu_callback_len", ``:word32``);
