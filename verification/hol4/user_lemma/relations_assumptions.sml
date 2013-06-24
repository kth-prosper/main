
(* take exceptions *)

val take_svc_exception_comb_thm =
   save_thm("take_svc_exception_comb_thm",
	   new_axiom("take_svc_exception_comb_thmX",
``preserve_relation_mmu (take_svc_exception <|proc := 0|>)
  (assert_mode 16w) (comb_mode 16w 19w)  priv_mode_constraints_v2 priv_mode_similar``));


val take_undef_instr_exception_comb_thm =
   save_thm("take_undef_instr_exception_comb_thm",
	   new_axiom("take_undef_instr_exception_comb_thmX",
``preserve_relation_mmu (take_undef_instr_exception <|proc := 0|>)
  (assert_mode 16w) (comb_mode 16w 27w)  priv_mode_constraints_v1 priv_mode_similar``));


val take_prefetch_abort_exception_comb_thm =
   save_thm("take_prefetch_abort_exception_comb_thm",
	   new_axiom("take_prefetch_abort_exception_comb_thmX",
``preserve_relation_mmu (take_prefetch_abort_exception <|proc := 0|>)
  (assert_mode 16w) (comb_mode 16w 23w)  priv_mode_constraints_v1 priv_mode_similar``));

val take_data_abort_exception_comb_thm =
   save_thm("take_data_abort_exception_comb_thm",
	   new_axiom("take_data_abort_exception_comb_thmX",
``preserve_relation_mmu (take_data_abort_exception <|proc := 0|>)
  (assert_mode 16w) (comb_mode 16w 23w)  priv_mode_constraints_v1 priv_mode_similar``));

val take_reset_comb_thm =
   save_thm("take_reset_comb_thm",
	   new_axiom("take_reset_comb_thmX",
``preserve_relation_mmu (take_reset <|proc := 0|>)
  (assert_mode 16w) (comb_mode 16w 23w)  priv_mode_constraints_v2 priv_mode_similar``));


val take_fiq_exception_comb_thm =
   save_thm("take_fiq_exception_comb_thm",
	   new_axiom("take_fiq_exception_comb_thmX",
``preserve_relation_mmu (take_fiq_exception <|proc := 0|>)
  (assert_mode 16w) (comb_mode 16w 17w)  priv_mode_constraints_v1 priv_mode_similar``));

val take_irq_exception_comb_thm =
   save_thm("take_irq_exception_comb_thm",
	   new_axiom("take_irq_exception_comb_thmX",
``preserve_relation_mmu (take_irq_exception <|proc := 0|>)
  (assert_mode 16w) (comb_mode 16w 18w)  priv_mode_constraints_v1 priv_mode_similar``));



