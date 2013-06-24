(**********************  simplifications ***************************)
(*******************  1. effects of reading   **********************)


val const_comp_def = Define `const_comp G = (!s s' x. ((G s = ValueState x s') ==> (s=s')))`;

val read_reg_constlem = store_thm(
    "read_reg_constlem",
    ``!n. const_comp (read_reg <|proc:=0|> n)``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
        THEN EVAL_TAC THEN (REPEAT (RW_TAC (srw_ss()) []
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN UNDISCH_ALL_TAC

                           THEN RW_TAC (srw_ss()) [])));

val read_sctlr_constlem = store_thm(
    "read_sctlr_constlem",
    ``const_comp (read_sctlr <|proc:=0|> )``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
        THEN EVAL_TAC THEN (REPEAT (RW_TAC (srw_ss()) []
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN UNDISCH_ALL_TAC
                           THEN RW_TAC (srw_ss()) [])));


val read_scr_constlem = store_thm(
    "read_scr_constlem",
    ``const_comp (read_scr <|proc:=0|> )``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
        THEN EVAL_TAC THEN (REPEAT (RW_TAC (srw_ss()) []
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN UNDISCH_ALL_TAC
                           THEN RW_TAC (srw_ss()) [])));


val exc_vector_base_constlem = store_thm(
    "exc_vector_base_constlem",
    ``const_comp (exc_vector_base <|proc:=0|> )``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
        THEN EVAL_TAC THEN (REPEAT (RW_TAC (srw_ss()) []
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN UNDISCH_ALL_TAC
                           THEN RW_TAC (srw_ss()) [])));



val read_cpsr_effect_lem = store_thm(
    "read_cpsr_effect_lem",
    ``!s H .  ((read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr))) s = (read_cpsr <|proc:=0|> >>= (\ (cpsr). H (s.psrs (0, CPSR)))) s)``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def] 
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]);



val read_cpsr_effect_fixed_lem = store_thm(
    "read_cpsr_effect_lem",
    ``!s H xI xF.  ((read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr with <|M := 16w; I:= xI; F:= xF|>))) s = (read_cpsr <|proc:=0|> >>= (\ (cpsr). H ((s.psrs (0, CPSR))  with <|M := 16w; I:= xI; F:= xF|> ))) s)``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def] 
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]);




val read_cpsr_par_effect_lem = store_thm(
    "read_cpsr_par_effect_lem",
    ``!s A H . (const_comp A) ==> (((A ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, cpsr))) s = ((A ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, s.psrs (0, CPSR)))) s)``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s` 
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]);


val read_cpsr_par_effect_fixed_lem = store_thm(
    "read_cpsr_par_effect_fixed_lem",
    ``!s A H xI xF. (const_comp A) ==> (((A ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, (cpsr with <|M := 16w; I:= xI; F:= xF|>) ))) s = ((A ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, (s.psrs (0, CPSR))  with <|M := 16w; I:= xI; F:= xF|>))) s)``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s` 
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]);



val read_cpsr_par_effect_with_16_lem = store_thm(
    "read_cpsr_par_effect_with_16_lem",
    ``!s A H. (const_comp A) ==> (((A ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, (cpsr with M := 16w) ))) s = ((A ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, (s.psrs (0, CPSR))  with M := 16w))) s)``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s` 
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]);


val read_cpsr_triple_par_effect_lem = store_thm(
    "read_cpsr_triple_par_effect_lem",
    ``!s A B H . (const_comp A) ==> ((((A ||| read_cpsr <|proc:=0|> ||| B) >>= (\ (a, cpsr, b). H (a, cpsr, b))) s) 
                                    = (((A ||| read_cpsr <|proc:=0|> ||| B) >>= (\ (a, cpsr, b). H (a, (s.psrs (0, CPSR)),b))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s` 
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]
       THEN Cases_on `B b`
       THEN RW_TAC (srw_ss()) []);


val read_cpsr_triple_par_effect_lem2 = store_thm(
    "read_cpsr_triple_par_effect_lem2",
    ``!s A B H . (const_comp A) ==> (const_comp B) ==> ((((A ||| B |||  read_cpsr <|proc:=0|>) >>= (\ (a, b, cpsr). H (a, b, cpsr))) s) 
                                    = (((A ||| B ||| read_cpsr <|proc:=0|>) >>= (\ (a, b, cpsr). H (a, b, (s.psrs (0, CPSR))))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s` 
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]);


val read_cpsr_triple_par_effect_with_16_lem = store_thm(
    "read_cpsr_triple_par_effect_with_16_lem",
    ``!s A B H . (const_comp A) ==> ((((A ||| read_cpsr <|proc:=0|> ||| B) >>= (\ (a, cpsr, b). H (a, (cpsr with M := 16w), b))) s) 
                                    = (((A ||| read_cpsr <|proc:=0|> ||| B) >>= (\ (a, cpsr, b). H (a, ((s.psrs (0, CPSR)) with M := 16w),b))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s` 
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]
       THEN Cases_on `B b`
       THEN RW_TAC (srw_ss()) []);


val read_cpsr_triple_par_effect_with_16_lem2 = store_thm(
    "read_cpsr_triple_par_effect_with_16_lem2",
    ``!s A B H . (const_comp A) ==> (const_comp B) ==> ((((A ||| B |||  read_cpsr <|proc:=0|>) >>= (\ (a, b, cpsr). H (a, b, (cpsr with M := 16w)))) s) 
                                    = (((A ||| B ||| read_cpsr <|proc:=0|>) >>= (\ (a, b, cpsr). H (a, b, ((s.psrs (0, CPSR)) with M := 16w)))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s` 
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]);

val read_cpsr_triple_par_effect_fixed_lem = store_thm(
    "read_cpsr_triple_par_effect_fixed_lem",
    ``!s A B H xI xF. (const_comp A) ==> ((((A ||| read_cpsr <|proc:=0|> ||| B) >>= (\ (a, cpsr, b). H (a, (cpsr with  <|M := 16w; I:= xI; F:= xF|>), b))) s) 
                                    = (((A ||| read_cpsr <|proc:=0|> ||| B) >>= (\ (a, cpsr, b). H (a, ((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>),b))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s` 
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]
       THEN Cases_on `B b`
       THEN RW_TAC (srw_ss()) []);


val read_cpsr_triple_par_effect_fixed_lem2 = store_thm(
    "read_cpsr_triple_par_effect_fixed_lem2",
    ``!s A B H xI xF. (const_comp A) ==> (const_comp B) ==> ((((A ||| B |||  read_cpsr <|proc:=0|>) >>= (\ (a, b, cpsr). H (a, b, (cpsr with <|M := 16w; I:= xI; F:= xF|>)))) s) 
                                    = (((A ||| B ||| read_cpsr <|proc:=0|>) >>= (\ (a, b, cpsr). H (a, b, ((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>)))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s` 
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]);






val read_cpsr_quintuple_par_effect_lem = store_thm(
    "read_cpsr_quintule_par_effect_lem",
    ``!s A B C D H . (const_comp A) ==>  (const_comp B) ==>  (const_comp C) ==>
                     ((((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D) >>= (\ (a, b, c, cpsr, d). H (a, b, c, cpsr, d))) s) 
                    = (((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D) >>= (\ (a, b, c, cpsr, d). H (a, b, c, (s.psrs (0, CPSR)), d))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s` 
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `C b'`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]
       THEN Cases_on `D b`
       THEN RW_TAC (srw_ss()) []);


val read_cpsr_quintuple_par_effect_lem2 = store_thm(
    "read_cpsr_quintule_par_effect_lem2",
    ``!s A B D E H . (const_comp A) ==>  (const_comp B) ==> 
                     ((((A ||| B ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, cpsr, d, e). H (a, b, cpsr, d, e))) s) 
                    = (((A ||| B ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, cpsr, d, e). H (a, b, (s.psrs (0, CPSR)), d, e))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s` 
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]   
       THEN Cases_on `D b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `E b'`
       THEN RW_TAC (srw_ss()) []);


val read_cpsr_quintuple_par_effect_with_16_lem = store_thm(
    "read_cpsr_quintule_par_effect_with_16_lem",
    ``!s A B C D H . (const_comp A) ==>  (const_comp B) ==>  (const_comp C) ==>
                     ((((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D) >>= (\ (a, b, c, cpsr, d). H (a, b, c, (cpsr with M := 16w), d))) s) 
                    = (((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D) >>= (\ (a, b, c, cpsr, d). H (a, b, c, ((s.psrs (0, CPSR)) with M := 16w), d))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s` 
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `C b'`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]
       THEN Cases_on `D b`
       THEN RW_TAC (srw_ss()) []);


val read_cpsr_quintuple_par_effect_with_16_lem2 = store_thm(
    "read_cpsr_quintule_par_effect_with_16_lem2",
    ``!s A B D E H . (const_comp A) ==>  (const_comp B) ==> 
                     ((((A ||| B ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, cpsr, d, e). H (a, b, (cpsr with M := 16w), d, e))) s) 
                    = (((A ||| B ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, cpsr, d, e). H (a, b, ((s.psrs (0, CPSR)) with M := 16w), d, e))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s` 
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]   
       THEN Cases_on `D b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `E b'`
       THEN RW_TAC (srw_ss()) []);



val read_cpsr_quintuple_par_effect_fixed_lem = store_thm(
    "read_cpsr_quintule_par_effect_fixed_lem",
    ``!s A B C D H xI xF. (const_comp A) ==>  (const_comp B) ==>  (const_comp C) ==>
                     ((((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D) >>= (\ (a, b, c, cpsr, d). H (a, b, c, (cpsr with <|M := 16w; I:= xI; F:= xF|>), d))) s) 
                    = (((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D) >>= (\ (a, b, c, cpsr, d). H (a, b, c, ((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>), d))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s` 
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `C b'`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]
       THEN Cases_on `D b`
       THEN RW_TAC (srw_ss()) []);


val read_cpsr_quintuple_par_effect_fixed_lem2 = store_thm(
    "read_cpsr_quintule_par_effect_fixed_lem2",
    ``!s A B D E H xI xF. (const_comp A) ==>  (const_comp B) ==> 
                     ((((A ||| B ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, cpsr, d, e). H (a, b, (cpsr with <|M := 16w; I:= xI; F:= xF|>), d, e))) s) 
                    = (((A ||| B ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, cpsr, d, e). H (a, b, ((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>), d, e))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s` 
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]   
       THEN Cases_on `D b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `E b'`
       THEN RW_TAC (srw_ss()) []);


val read_reg_read_cpsr_par_effect_lem = store_thm(
    "read_reg_read_cpsr_par_effect_lem",
    ``!s n H. ((read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, cpsr ))) s = ((read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, s.psrs (0, CPSR)))) s``,
    RW_TAC (srw_ss()) [read_reg_constlem, read_cpsr_par_effect_lem]);



val read_reg_read_cpsr_par_effect_fixed_lem = store_thm(
    "read_reg_read_cpsr_par_effect_fixed_lem",
    ``!s n H xI xF. ((read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, (cpsr with <|M := 16w; I:= xI; F:= xF|>)))) s = ((read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>= (\ (b, cpsr). H (b, ((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>) ))) s``,
    RW_TAC (srw_ss()) [read_reg_constlem, read_cpsr_par_effect_fixed_lem]);



(**********************  simplifications ***************************)
(************  2. computations applied to states   *****************)


val cpsr_simp_lem = store_thm(
    "cpsr_simp_lem",
    ``!s H . (assert_mode 16w s) ==> 
       (((read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr))) s)
      = ((read_cpsr <|proc:=0|> >>= (\ (cpsr). H ((s.psrs (0, CPSR)) with M := 16w))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_cpsr_effect_lem, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with M:= 16w))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);


val cpsr_simp_ext_lem = store_thm(
    "cpsr_simp_ext_lem",
    ``!s H. (assert_mode 16w s) ==> 
             ((s.psrs(0,CPSR)).I = xI) ==>
             ((s.psrs(0,CPSR)).F = xF) ==>
       (((read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr))) s)
      = ((read_cpsr <|proc:=0|> >>= (\ (cpsr). H ((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_cpsr_effect_lem, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with <|I := (s.psrs (0,CPSR)).I; F := (s.psrs (0,CPSR)).F; M := 16w|>))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);


val cpsr_par_simp_lem = store_thm(
    "cpsr_par_simp_lem",
    ``!s H n. (assert_mode 16w s) ==> 
       ((((read_reg <|proc:=0|> n  ||| read_cpsr <|proc:=0|>) >>= (\ (a, cpsr). H (a, cpsr))) s)
      = (((read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>= (\ (a, cpsr). H (a, (s.psrs (0, CPSR)) with M := 16w))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_reg_constlem, read_cpsr_par_effect_lem, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with M:= 16w))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);


val cpsr_triple_simp_ext_lem = store_thm(
    "cpsr_triple_simp_ext_lem",
    ``!s H . (assert_mode 16w s) ==> 
             ((s.psrs(0,CPSR)).I = xI) ==>
             ((s.psrs(0,CPSR)).F = xF) ==>
       ((((read_reg <|proc:=0|> 15w ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (b,cpsr,d). H (b,cpsr,d))) s)
      = (((read_reg <|proc:=0|> 15w ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (b,cpsr,d). H (b,((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>),d))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_reg_constlem, read_cpsr_triple_par_effect_lem, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with <|I := (s.psrs (0,CPSR)).I; F := (s.psrs (0,CPSR)).F; M := 16w|>))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);


val cpsr_triple_simp_ext_lem2 = store_thm(
    "cpsr_triple_simp_ext_lem2",
    ``!s H . (assert_mode 16w s) ==> 
             ((s.psrs(0,CPSR)).I = xI) ==>
             ((s.psrs(0,CPSR)).F = xF) ==>
       ((((read_sctlr <|proc := (0 :num)|>
          ||| read_scr <|proc := (0 :num)|>
          |||  read_cpsr <|proc:=0|> ) >>= (\ (sctlr,scr,cpsr). H (sctlr,scr,cpsr))) s)
      = (((read_sctlr <|proc := (0 :num)|>
          ||| read_scr <|proc := (0 :num)|>
          |||  read_cpsr <|proc:=0|> ) >>= (\ (sctlr,scr,cpsr). H (sctlr,scr,((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|> )))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_sctlr_constlem, read_scr_constlem, read_cpsr_triple_par_effect_lem2, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with <|I := (s.psrs (0,CPSR)).I; F := (s.psrs (0,CPSR)).F; M := 16w|> ))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);


val cpsr_quintuple_simp_ext_lem = store_thm(
    "cpsr_quintuple_simp_ext_lem",
    ``!s H a n m. (assert_mode 16w s) ==> 
             ((s.psrs(0,CPSR)).I = xI) ==>
             ((s.psrs(0,CPSR)).F = xF) ==>
       ((((read_reg <|proc:=0|> a ||| read_reg <|proc:=0|> n ||| read_reg <|proc:=0|> m ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (a, b, c, cpsr, d). H (a, b, c, cpsr, d))) s)
      = (((read_reg <|proc:=0|> a ||| read_reg <|proc:=0|> n ||| read_reg <|proc:=0|> m ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (a, b, c, cpsr, d). H (a, b, c, ((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>), d))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_reg_constlem, read_cpsr_quintuple_par_effect_lem, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with <|I := (s.psrs (0,CPSR)).I; F := (s.psrs (0,CPSR)).F; M := 16w|>))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);


val cpsr_quintuple_simp_ext_lem2 = store_thm(
    "cpsr_quintuple_simp_ext_lem2",
    ``!s H x . (assert_mode 16w s) ==> 
             ((s.psrs(0,CPSR)).I = xI) ==>
             ((s.psrs(0,CPSR)).F = xF) ==>
       ((((read_reg <|proc:=0|> x ||| exc_vector_base <|proc:=0|> ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= (\ (a, b, cpsr, d, e). H (a, b, cpsr, d, e))) s)
      = (((read_reg <|proc:=0|> x ||| exc_vector_base <|proc:=0|> ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= (\ (a, b, cpsr, d, e). H (a, b, ((s.psrs (0, CPSR)) with <|M := 16w; I:= xI; F:= xF|>), d, e))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_reg_constlem, exc_vector_base_constlem, read_cpsr_quintuple_par_effect_lem2, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with <|I := (s.psrs (0,CPSR)).I; F := (s.psrs (0,CPSR)).F; M := 16w|>))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);




(**********************  simplifications ***************************)
(******  3. computations wrapped by preserving predicate   *********)


fun CPSR_SIMP_TAC simp_ext_lem const_lem_list H_sig effect_fixed_lem additional_spec_list =
    RW_TAC (srw_ss()) []
       THEN EQ_TAC 
       THEN RW_TAC (srw_ss()) [preserve_relation_mmu_def, fix_flags_def, fixed_flags_def]
       THEN RW_TAC (srw_ss()) const_lem_list 
       THEN SPEC_ASSUM_TAC (``!g s1 s2. X``, [``g:word32``, ``s1:arm_state``, ``s2:arm_state``])
       THEN NTAC 2 (UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [assert_mode_def])
       THENL[ DISJ1_TAC
               THEN MAP_EVERY EXISTS_TAC [``a:'a``, ``s1':arm_state``, ``s2'':arm_state``],
              DISJ2_TAC
               THEN EXISTS_TAC ``e:string``,
              DISJ1_TAC
               THEN MAP_EVERY EXISTS_TAC [``a:'a``, ``s1':arm_state``, ``s2'':arm_state``],
              DISJ2_TAC
               THEN EXISTS_TAC ``e:string``]
       THEN ASSUME_TAC (SPECL [``xI:bool``, ``(s2.psrs (0,CPSR)).F:bool``, ``s1:arm_state``, mk_var ("H", H_sig)]  (GEN_ALL simp_ext_lem))
       THEN ASSUME_TAC (SPECL [``xI:bool``, ``(s2.psrs (0,CPSR)).F:bool``, ``s2:arm_state``, mk_var ("H", H_sig)]  (GEN_ALL simp_ext_lem))
       THEN ASSUME_TAC (SPECL (List.concat [[``s1:arm_state``], additional_spec_list, [mk_var ("H", H_sig), ``xI:bool``, ``(s2.psrs (0,CPSR)).F:bool``]]) effect_fixed_lem)
       THEN ASSUME_TAC (SPECL (List.concat [[``s2:arm_state``], additional_spec_list, [mk_var ("H", H_sig), ``xI:bool``, ``(s2.psrs (0,CPSR)).F:bool``]])  effect_fixed_lem)
       THEN SPEC_ASSUM_TAC (``!(a:word4) (n:word4) (m:word4). X``, [``aa:word4``, ``nn:word4``, ``mm:word4``])        THEN SPEC_ASSUM_TAC (``!(x:word4). X``, [``x:word4``])  (* dirty hack for the quintuple cases *)
       THEN UNDISCH_ALL_TAC 
       THEN RW_TAC (srw_ss()) [assert_mode_def]
       THEN FULL_SIMP_TAC (srw_ss()) const_lem_list;


val cpsr_simp_rel_lem = store_thm(
    "cpsr_simp_rel_lem",
    ``!H inv2 uf uy. 
       (preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr))) (assert_mode 16w) (inv2) uf uy)
      = (preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr with M := 16w)))(assert_mode 16w) (inv2) uf uy)``,
     RW_TAC (srw_ss()) [cpsr_simp_lem, preserve_relation_mmu_def]);


val cpsr_simp_rel_ext_lem = store_thm(
    "cpsr_simp_rel_ext_lem",
    ``!H inv2 uf uy xI xF. 
       (preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr))) (assert_mode 16w) (inv2) uf (fix_flags xI xF uy))
      = (preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr with <|M := 16w; I:= xI; F:= xF|>)))(assert_mode 16w) (inv2) uf (fix_flags xI xF uy))``,
    CPSR_SIMP_TAC cpsr_simp_ext_lem
                  [read_reg_constlem]
                  ``:(ARMpsr ->('a M))``
                  (read_cpsr_effect_fixed_lem)
                  ([]:Parse.term list));

val cpsr_par_simp_rel_lem = store_thm(
    "cpsr_simp_rel_lem",
    ``!n H inv2 uf uy. 
       (preserve_relation_mmu ((read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>= (\ (a, cpsr). H (a, cpsr))) (assert_mode 16w) (inv2) uf uy)
      = (preserve_relation_mmu ((read_reg <|proc:=0|> n ||| read_cpsr <|proc:=0|>) >>= (\ (a, cpsr). H (a, cpsr with M := 16w)))(assert_mode 16w) (inv2) uf uy)``,
     RW_TAC (srw_ss()) [cpsr_par_simp_lem, preserve_relation_mmu_def, read_reg_constlem, read_cpsr_par_effect_with_16_lem]);
 




val cpsr_triple_simp_rel_ext_lem = store_thm(
    "cpsr_triple_simp_rel_ext_lem",
    ``!H inv2 uf uy xI xF.  
       (preserve_relation_mmu ((read_reg <|proc:=0|> 15w ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (b,cpsr,d). H (b,cpsr,d))) (assert_mode 16w) (inv2) uf (fix_flags xI xF uy))
      = (preserve_relation_mmu ((read_reg <|proc:=0|> 15w ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (b,cpsr,d). H (b,(cpsr with <|M := 16w; I:= xI; F:= xF|>),d))) (assert_mode 16w) (inv2) uf (fix_flags xI xF uy))``,
    CPSR_SIMP_TAC cpsr_triple_simp_ext_lem
                  [(SPEC ``15w:word4`` read_reg_constlem)]
                  ``:(word32 # ARMpsr # word32 ->('a M))``
                  (INST_TYPE [alpha |-> Type `:word32`, beta |-> Type `:word32`, gamma |-> alpha] read_cpsr_triple_par_effect_fixed_lem)
                  [``(read_reg <|proc := 0|> 15w):(word32 M)``, ``(read_teehbr <|proc := 0|>):(word32 M)``]);



val cpsr_triple_simp_rel_ext_lem2 = store_thm(
    "cpsr_triple_simp_rel_ext_lem2",
    ``!H inv2 uf uy xI xF.  
       (preserve_relation_mmu ((read_sctlr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_cpsr <|proc:=0|>) >>= (\ (a,b,cpsr). H (a,b,cpsr))) (assert_mode 16w) (inv2)  uf (fix_flags xI xF uy))
      = (preserve_relation_mmu ((read_sctlr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_cpsr <|proc:=0|>) >>= (\ (a,b,cpsr). H (a,b,(cpsr with <|M := 16w; I:= xI; F:= xF|>)))) (assert_mode 16w) (inv2) uf (fix_flags xI xF uy))``,
    CPSR_SIMP_TAC cpsr_triple_simp_ext_lem2
                  [read_sctlr_constlem, read_scr_constlem]
                  ``:(CP15sctlr # CP15scr # ARMpsr ->('a M))``
                  (INST_TYPE [alpha |-> Type `:CP15sctlr`, beta |-> Type `:CP15scr`, gamma |-> alpha] read_cpsr_triple_par_effect_fixed_lem2)
                  [``(read_sctlr <|proc := 0|>):(CP15sctlr M)``, ``(read_scr <|proc := 0|>):(CP15scr M)``]);



val cpsr_quintuple_simp_rel_ext_lem = store_thm(
    "cpsr_quintuple_simp_rel_ext_lem",
    ``!aa nn mm H inv2 uf uy xI xF . 
       (preserve_relation_mmu ((read_reg <|proc:=0|> aa ||| read_reg <|proc:=0|> nn ||| read_reg <|proc:=0|> mm ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (aa, bb, cc, cpsr, dd). H (aa, bb, cc, cpsr, dd))) (assert_mode 16w) (inv2)  uf (fix_flags xI xF uy))
      = (preserve_relation_mmu ((read_reg <|proc:=0|> aa ||| read_reg <|proc:=0|> nn ||| read_reg <|proc:=0|> mm ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (aa, bb, cc, cpsr, dd). H (aa, bb, cc, (cpsr with <|M := 16w; I:= xI; F:= xF|>), dd))) (assert_mode 16w) (inv2)  uf (fix_flags xI xF uy))``,
    CPSR_SIMP_TAC cpsr_quintuple_simp_ext_lem
                  [read_reg_constlem]
                  ``:(word32 # word32 # word32 # ARMpsr # word32->('a M))``
                  (INST_TYPE [alpha |-> Type `:word32`, beta |-> Type `:word32`, gamma |-> Type `:word32`, delta |-> Type `:word32`, Type `:'e` |-> alpha] read_cpsr_quintuple_par_effect_fixed_lem)
                  [``(read_reg <|proc:=0|> aa) :word32 M``, ``(read_reg <|proc:=0|> nn) :word32 M`` , ``(read_reg <|proc:=0|> mm) :word32 M`` , ``(read_teehbr <|proc:=0|> ):word32 M`` ]);


val cpsr_quintuple_simp_rel_ext_lem2 = store_thm(
    "cpsr_quintuple_simp_rel_ext_lem2",
    ``!x H inv2 uf uy xI xF.
       (preserve_relation_mmu (((read_reg <|proc:=0|> x ||| exc_vector_base <|proc:=0|> ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= (\ (a, b, cpsr, d, e). H (a, b, cpsr, d, e)))) (assert_mode 16w) (inv2)  uf (fix_flags xI xF uy))
      = (preserve_relation_mmu (((read_reg <|proc:=0|> x ||| exc_vector_base <|proc:=0|> ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= (\ (a, b, cpsr, d, e). H (a, b, (cpsr with <|M := 16w; I:= xI; F:= xF|>), d, e))))(assert_mode 16w) (inv2)  uf (fix_flags xI xF uy))``,
  CPSR_SIMP_TAC cpsr_quintuple_simp_ext_lem2
                  [read_reg_constlem, exc_vector_base_constlem, read_scr_constlem, read_sctlr_constlem]
                  ``:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr ->('a M))``
                  (INST_TYPE [alpha |-> Type `:word32`, beta |-> Type `:word32`, gamma |-> Type `:CP15scr`, delta |-> Type `:CP15sctlr`, Type `:'e` |-> alpha] read_cpsr_quintuple_par_effect_fixed_lem2)
                  [``(read_reg <|proc:=0|> x) :word32 M``, ``(exc_vector_base <|proc:=0|>) :word32 M`` , ``(read_scr <|proc:=0|>) :CP15scr M`` , ``(read_sctlr <|proc:=0|> ):CP15sctlr M`` ]);



