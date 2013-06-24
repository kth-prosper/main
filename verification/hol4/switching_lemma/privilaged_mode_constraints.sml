fun decompose_term a =
    let val (opr, acs) =    
	    case dest_term a of
		(LAMB (b,c)) => 
	     	strip_comb c
	      | (* (COMB (b,c)) *) _ => 
				   strip_comb a
    in		     
	if (length acs < 2) then
	    (opr,opr,opr)
	else
	    let val l = List.nth(acs,0) 
		val r = List.nth(acs,1)
	    in			 
		if (same_const opr  (``$>>=``)) 
		then
		    let val (_,r_body) = pairLib.dest_pabs r
		    in
			(l,r,r_body)
		    end
		else 
		    if (same_const opr ``$|||``)
		    then
			(l,r,r)
		    else (opr,opr,opr)
	    end
    end;
    

fun define_pfc_goal a expr = 
    set_goal([], ``
	    (priv_flags_constraints ^a ^expr) ``);
	
fun define_pfc_goal_abs a expr = 
    set_goal([], ``
	    (priv_flags_constraints_abs ^a ^expr) ``);
	

(*    borrowed from Oliver    *)
val const_comp_def = Define `const_comp G = (!s s' x. ((G s = ValueState x s') ==> (s=s')))`;

val read_reg_constlem = 
    store_thm(
    "read_reg_constlem",
    ``!n. const_comp (read_reg <|proc:=0|> n)``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
		  THEN EVAL_TAC THEN (REPEAT (RW_TAC (srw_ss()) []
						     THEN FULL_SIMP_TAC (srw_ss()) []
						     THEN UNDISCH_ALL_TAC
						     
						     THEN RW_TAC (srw_ss()) [])));

val read_sctlr_constlem = 
    store_thm(
    "read_sctlr_constlem",
    ``const_comp (read_sctlr <|proc:=0|> )``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
		  THEN EVAL_TAC 
		  THEN (REPEAT (RW_TAC (srw_ss()) []
				       THEN FULL_SIMP_TAC (srw_ss()) []
				       THEN UNDISCH_ALL_TAC
				       THEN RW_TAC (srw_ss()) [])));


val read_scr_constlem = 
    store_thm(
    "read_scr_constlem",
    ``const_comp (read_scr <|proc:=0|> )``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
		  THEN EVAL_TAC 
		  THEN (REPEAT 
			    (RW_TAC (srw_ss()) []
				    THEN FULL_SIMP_TAC (srw_ss()) []
				    THEN UNDISCH_ALL_TAC
				    THEN RW_TAC (srw_ss()) [])));
    

val exc_vector_base_constlem = 
    store_thm(
    "exc_vector_base_constlem",
    ``const_comp (exc_vector_base <|proc:=0|> )``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
		  THEN EVAL_TAC 
		  THEN (REPEAT (RW_TAC (srw_ss()) []
				       THEN FULL_SIMP_TAC (srw_ss()) []
				       THEN UNDISCH_ALL_TAC
				       THEN RW_TAC (srw_ss()) [])));




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

val cpsr_quintuple_simp_lem = store_thm(
    "cpsr_quintuple_simp_lem",
    ``!s a n m H . (assert_mode 16w s) ==> 
       ((((read_reg <|proc:=0|> a ||| read_reg <|proc:=0|> n ||| read_reg <|proc:=0|> m ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (a, b, c, cpsr, d). H (a, b, c, cpsr, d))) s)
      = (((read_reg <|proc:=0|> a ||| read_reg <|proc:=0|> n ||| read_reg <|proc:=0|> m ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (a, b, c, cpsr, d). H (a, b, c, ((s.psrs (0, CPSR)) with M := 16w), d))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_reg_constlem, read_cpsr_quintuple_par_effect_lem, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with M:= 16w))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);


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


val cpsr_quintuple_simp_rel_lem = store_thm(
    "cpsr_quintuple_simp_rel_lem",
    ``!a n m H inv2 uf uy. 
       (preserve_relation_mmu ((read_reg <|proc:=0|> a ||| read_reg <|proc:=0|> n ||| read_reg <|proc:=0|> m ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (pc, b, c, cpsr, d). H (pc, b, c, cpsr, d))) (assert_mode 16w) (inv2) uf uy)
      = (preserve_relation_mmu ((read_reg <|proc:=0|> a ||| read_reg <|proc:=0|> n ||| read_reg <|proc:=0|> m ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (pc, b, c, cpsr, d). H (pc, b, c, (cpsr with M := 16w), d))) (assert_mode 16w) (inv2) uf uy)``,
    RW_TAC (srw_ss()) [cpsr_quintuple_simp_lem, preserve_relation_mmu_def, read_reg_constlem, read_cpsr_quintuple_par_effect_with_16_lem]);


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


val cpsr_quintuple_simp_lem2 = store_thm(
    "cpsr_quintuple_simp_lem2",
    ``!s x H . (assert_mode 16w s) ==> 
       ((((read_reg <|proc:=0|> x ||| exc_vector_base <|proc:=0|> ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= (\ (a, b, cpsr, d, e). H (a, b, cpsr, d, e))) s)
      = (((read_reg <|proc:=0|> x ||| exc_vector_base <|proc:=0|> ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= (\ (a, b, cpsr, d, e). H (a, b, ((s.psrs (0, CPSR)) with M := 16w), d, e))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_reg_constlem, exc_vector_base_constlem, read_cpsr_quintuple_par_effect_lem2, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with M:= 16w))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);


val cpsr_quintuple_simp_rel_lem2 = store_thm(
    "cpsr_quintuple_simp_rel_lem2",
    ``!x H inv2 uf uy.
       (preserve_relation_mmu (((read_reg <|proc:=0|> x ||| exc_vector_base <|proc:=0|> ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= (\ (pc, ExcVectorBase, cpsr, scr, sctlr). H (pc, ExcVectorBase, cpsr, scr, sctlr)))) (assert_mode 16w) (inv2) uf uy)
      = (preserve_relation_mmu (((read_reg <|proc:=0|> x ||| exc_vector_base <|proc:=0|> ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= (\ (pc, ExcVectorBase, cpsr, scr, sctlr). H (pc, ExcVectorBase, (cpsr with M := 16w), scr, sctlr))))(assert_mode 16w) (inv2) uf uy)``,
    RW_TAC (srw_ss()) [cpsr_quintuple_simp_lem2, preserve_relation_mmu_def, read_reg_constlem, exc_vector_base_constlem, read_cpsr_quintuple_par_effect_with_16_lem2]);


val read_cpsr_effect_lem = store_thm(
    "read_cpsr_effect_lem",
    ``!s H .  ((read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr))) s = (read_cpsr <|proc:=0|> >>= (\ (cpsr). H (s.psrs (0, CPSR)))) s)``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def] 
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, readT_def]);


val cpsr_simp_lem = store_thm(
    "cpsr_simp_lem",
    ``!s H u. (assert_mode u s) ==> 
       (((read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr))) s)
      = ((read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr with M := u))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_cpsr_effect_lem, ARM_READ_CPSR_def]
       THEN `s.psrs (0,CPSR) = s.psrs (0,CPSR) with M := (s.psrs (0,CPSR)).M` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);

val cpsr_simp_rel_lem = store_thm(
    "cpsr_simp_rel_lem",
    ``!H inv2 uf uy u. 
       (preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr))) (assert_mode u) (inv2) uf uy)
      = (preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr with M := u)))(assert_mode u) (inv2) uf uy)``,
     RW_TAC (srw_ss()) [preserve_relation_mmu_def]
	    THEN  METIS_TAC [cpsr_simp_lem]);

(***************** from Oliver: Should be removed *****************)
val keep_mode_relation_def = Define `keep_mode_relation comp i1 i2 = 
  (!g s s' x. (mmu_requirements s g) ==> (i1 s) ==> (comp s = ValueState x s') ==> (i2 s'))`;

val keep_similar_relation_def = Define `keep_similar_relation comp invr1 y = 
    !g s1 s2.
    mmu_requirements s1 g    ==>
    mmu_requirements s2 g    ==>
    similar g s1 s2          ==>
    (y  g s1 s2)            ==>
    invr1 s1                 ==>
    invr1 s2                 ==>
    ((?a s1' s2'.((comp s1 = ValueState a s1') /\  (comp s2 = ValueState a s2') /\
           (y  g s1' s2') /\        (similar g s1' s2')))
\/   (? e. (comp s1 = Error e) /\ (comp s2 = Error e)))`;

val keep_untouched_relation_def = Define `keep_untouched_relation comp invr1 f =
    !g s s' a. (mmu_requirements s g) ==> (invr1 s) ==> (comp s = ValueState a s') ==> ((untouched g s s') /\  (f g s s'))`;

val three_parts_thm = store_thm(
    "three_parts_thm",
    ``!comp i1 i2 f y. (keep_mode_relation comp i1 i2) ==> (keep_similar_relation comp i1 y) ==> (keep_untouched_relation comp i1 f) ==> (preserve_relation_mmu comp i1 i2 f y)``,
    RW_TAC (srw_ss()) [preserve_relation_mmu_def, keep_mode_relation_def, keep_similar_relation_def, keep_untouched_relation_def] THEN METIS_TAC []);

val refl_rel_def = Define `refl_rel y = (!gg ss. y gg ss ss)`;

val downgrade_thm = store_thm (
    "downgrade_thm",
    ``!comp i1 i2 f y. (preserve_relation_mmu comp i1 i2 f y) ==> (refl_rel y)
       ==> (keep_mode_relation comp i1 i2 /\ keep_similar_relation comp i1 y /\ keep_untouched_relation comp i1 f)``,
    RW_TAC (srw_ss()) [refl_rel_def, preserve_relation_mmu_def, keep_mode_relation_def, keep_similar_relation_def, keep_untouched_relation_def]
       THEN RES_TAC
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN (TRY (METIS_TAC []))
       THEN ASSUME_TAC (SPECL [``g:word32``, ``s:arm_state``] similar_refl)
       THEN SPEC_ASSUM_TAC (``!gg ss. y gg ss``, [``g:word32``, ``s:arm_state``])
       THEN RES_TAC
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN METIS_TAC []);
(*********************************************************************)

(* End of borrowed theorems *)




val ASSUME_SPECL_TAC = 
fn l => fn thm => ASSUME_TAC (SPECL l thm);

val ASSUME_SIMP_TAC = 
fn l => fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) l thm);

val IMP_RES_SIMP_TAC = 
fn l => fn thm => IMP_RES_TAC (SIMP_RULE (srw_ss()) l thm);


val ASSUME_SPEC_TAC = 
fn l => fn thm => ASSUME_TAC (SPEC l thm);


val ASSUME_SPECL_SIMP_TAC = 
fn l => fn sthms => fn thm => ASSUME_TAC (SPECL l (SIMP_RULE (srw_ss()) sthms thm));

val IMP_RES_SPEC_TAC = 
fn l => fn thm => IMP_RES_TAC (SPEC l thm);

val IMP_RES_SPECL_TAC = 
fn l => fn thm => IMP_RES_TAC (SPECL l thm);

val MP_SPEC_TAC = 
fn l => fn thm => MP_TAC (SPEC l thm);

val MP_SPECL_TAC = 
fn l => fn thm => MP_TAC (SPECL l thm);

val ASSUME_SPECL_INST_TAC =  
 fn sl => fn tl => fn thm =>
	     ASSUME_TAC (SPECL sl (INST_TYPE tl thm)) 


val ASSUME_SPECL_GEN_REWRITE_TAC =
 fn (l , thm, simps) => ASSUME_TAC (SPECL 
					l (GEN_ALL (REWRITE_RULE simps thm)));

(*******should be defined as local *************)

val mk_spec_list =
 fn a =>  
    [``(SND (SND (SND (SND ^a)))):CP15sctlr``,
     ``(FST (SND (SND (SND ^a)))):CP15scr``,
     ``(FST (^a)):word32``,
     ``(FST (SND (SND (^a)))):ARMpsr``,
     ``FST (SND ^a):word32``
    ];	    
val mk_spec_list2 = 
 fn a => 
    [``(SND (SND (SND (SND ^a)))):CP15sctlr``,
     ``(FST (SND (SND (SND (^a))))):CP15scr``,
     ``(FST (SND (SND (^a)))):ARMpsr``,
     ``FST (SND ^a):word32``,
     ``(FST (^a)):word32``
    ];	
    
val mk_spec_list3 = 
 fn a => 
    [``(SND (SND (SND (SND (SND ^a))))):CP15sctlr``,
     ``(FST (SND (SND (SND (SND ^a))))):CP15scr``,
     ``(FST (^a)):word32``,
     ``(FST (SND (SND (^a)))):bool``,
     ``(FST (SND (SND (SND (^a))))):ARMpsr``,
     ``(FST (SND ^a)):word32``
    ];	    

val mk_spec_list4 = 
 fn a => 
    [``(SND (SND (SND (SND (SND ^a))))):CP15sctlr``,
     ``(FST (SND (SND (SND (SND ^a))))):CP15scr``,
     ``(FST (SND (SND (SND (^a))))):ARMpsr``,
     ``(FST (SND (SND (^a)))):bool``,
     ``(FST (SND ^a)):word32``,
     ``(FST (^a)):word32``
    ];	



val read_cpsr_constlem = 
    store_thm(
    "read_cpsr_constlem",
    ``const_comp (read_cpsr <|proc:=0|> )``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
		  THEN EVAL_TAC 
		  THEN (REPEAT (RW_TAC (srw_ss()) []
				       THEN FULL_SIMP_TAC (srw_ss()) []
				       THEN UNDISCH_ALL_TAC
				       THEN RW_TAC (srw_ss()) [])));

val  parT_const_comp_thm = 
     store_thm(
     "parT_const_comp_thm", 
     ``! f h. const_comp f ==>
	      const_comp h ==>
	      const_comp (f ||| h)``
   ,
   RW_TAC (srw_ss()) [parT_def,seqT_def,const_comp_def,constT_def] THEN
	  Cases_on ` f s ` THEN 
	  RES_TAC THEN 
	  FULL_SIMP_TAC (srw_ss()) [] THEN 
	  Cases_on ` h b ` THEN 
	  RES_TAC THEN 
	  FULL_SIMP_TAC (srw_ss()) [] THEN 
	  RW_TAC (srw_ss()) [] THEN 
	  Cases_on ` access_violation b` THEN 
	  FULL_SIMP_TAC (srw_ss()) []);


val  fixed_sctrl_undef_svc_thm1 = 
     store_thm(
     "fixed_sctrl_undef_svc_thm1",
     ``!s A B C D H . 
	      (const_comp A) ==> 
	      (const_comp B) ==>
	      (const_comp C) ==>
	      (const_comp D) ==>
	      ((((A ||| B ||| C ||| D 
		    ||| read_sctlr <|proc:=0|>) >>=
					   (\ (a, b, c, d, e). H (a, b, c, d, e))) s)
	       = (((A ||| B ||| C ||| D ||| 
		      read_sctlr <|proc:=0|>) >>= 
				 (\ (a, b, c, d, e). H (a, b, c, d, s.coprocessors.state.cp15.SCTLR))) s))
``,
     RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
	    THEN Cases_on `A s` 
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `B s` 
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `C s` 
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `D s` 
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN FULL_SIMP_TAC (srw_ss()) [read_sctlr_def,readT_def]
	    THEN RW_TAC (srw_ss())  []
     );

val  fixed_cpsr_undef_svc_thm1 = 
     store_thm(
     "fixed_cpsr_undef_svc_thm1",
     ``!s A B C D H . 
	      (const_comp A) ==> 
	      (const_comp B) ==>
	      ((((A ||| B ||| read_cpsr <|proc := 0|> ||| C ||| D) >>=
					   (\ (a, b, c, d, e). H (a, b, c, d, e))) s)
	       = (((A ||| B ||| read_cpsr <|proc := 0|> ||| C ||| D) >>= 
				 (\ (a, b, c, d, e). H (a, b, s.psrs (0,CPSR), d, e))) s))
``,
     RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
	    THEN Cases_on `A s` 
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `B s` 
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN FULL_SIMP_TAC (srw_ss()) [read_cpsr_def,read__psr_def,readT_def]
	    THEN RW_TAC (srw_ss())  []
	    THEN Cases_on `C b` 
	    THEN Cases_on ` access_violation b'`
	    THEN FULL_SIMP_TAC (srw_ss())  []
	    THEN Cases_on `D b'` 
	    THEN Cases_on ` access_violation b''`
	    THEN FULL_SIMP_TAC (srw_ss())  []
   
     );

val  fixed_sctrl_abt_irq_thm1 = 
     store_thm(
     "fixed_sctrl_abt_irq_thm1",
     ``!s A B C D E H . 
	      (const_comp A) ==> 
	      (const_comp B) ==>
	      (const_comp C) ==>
	      (const_comp D) ==>
	      (const_comp E) ==>
	      ((((A ||| B ||| C ||| D ||| E 
		    ||| read_sctlr <|proc:=0|>) >>=
					   (\ (a, b, c, d, e,f). H (a, b, c, d, e,f))) s)
	       = (((A ||| B ||| C ||| D ||| E |||  
		      read_sctlr <|proc:=0|>) >>= 
				 (\ (a, b, c, d, e,f). H (a, b, c, d, e, s.coprocessors.state.cp15.SCTLR))) s))
``,
     RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
	    THEN Cases_on `A s` 
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `B s` 
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `C s` 
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `D s` 
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `E s` 
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN FULL_SIMP_TAC (srw_ss()) [read_sctlr_def,readT_def]
	    THEN RW_TAC (srw_ss())  []
     );


val  fixed_undef_svc_exception_rp_thm2 = store_thm(
    "fixed_undef_svc_exception_rp_thm2",
    ``!s e d c b a.
	  (~access_violation s) ==>
	  (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> |||
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
           read_sctlr <|proc:=0|>) s)
	= ValueState (a, b, c, d, e) s) ==>
	  ((a = get_pc_value s)
	   /\
		(b=get_base_vector_table s(* if s.coprocessors.state.cp15.SCTLR.V then *)
		   (*     0xFFFF0000w :bool[32] *)
		   (* else *)
		   (*     0w  *)
		 )
	   /\
		(c=s.psrs (0,CPSR ))
	   /\
		(d=s.coprocessors.state.cp15.SCR)
	   /\
		(e=s.coprocessors.state.cp15.SCTLR))``,
    EVAL_TAC
	THEN RW_TAC (srw_ss())  []
				       );

     
val  fixed_abort_irq_exception_rp_thm2 = store_thm(
    "fixed_abort_irq_exception_rp_thm2",
    ``!s f e d c b a .
	  (~access_violation s) ==>
	  (* (Extension_Security ∉ s.information.extensions) ==> *)
	  (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> ||| have_security_ext <|proc:=0|>
        ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) s)
	= (ValueState (a, b, c, d, e, f) s)) ==>
	  ((a = get_pc_value s)
	   /\
		(b=get_base_vector_table s)
	   /\
	   	(c = (((ARMarch2num s.information.arch = 5) ∨
         (ARMarch2num s.information.arch = 7)) ∧
        Extension_Security ∈ s.information.extensions))
	   /\
	(d=s.psrs (0,CPSR ))
	   /\
		(e=s.coprocessors.state.cp15.SCR)
	   /\
		(f=s.coprocessors.state.cp15.SCTLR))``,
    EVAL_TAC
	THEN RW_TAC (srw_ss())  []);

val have_security_ext_constlem = 
    store_thm(
    "have_security_ext_constlem",
    ``const_comp (have_security_ext <|proc := 0|>)``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
		  THEN EVAL_TAC THEN (REPEAT (RW_TAC (srw_ss()) []
						     THEN FULL_SIMP_TAC (srw_ss()) []
						     THEN UNDISCH_ALL_TAC
						     
						     THEN RW_TAC (srw_ss()) [])));

val const_comp_take_undef_svc_exception_rp_thm = 
    store_thm(
    "const_comp_take_undef_svc_exception_rp_thm", 
    ``const_comp (read_reg <|proc := 0|> 15w
	          ||| exc_vector_base <|proc := 0|>
		  ||| read_cpsr <|proc := 0|> ||| read_scr <|proc := 0|>
		  ||| read_sctlr <|proc := 0|>)``,
    ASSUME_TAC (SPEC ``15w:bool[4]`` read_reg_constlem) 
	       THEN ASSUME_TAC read_cpsr_constlem
	       THEN ASSUME_TAC exc_vector_base_constlem
	       THEN ASSUME_TAC read_scr_constlem
	       THEN ASSUME_TAC read_sctlr_constlem
	       THEN 
	       `const_comp (read_scr <|proc := 0|>
						||| read_sctlr <|proc := 0|>)` by 
	       IMP_RES_TAC parT_const_comp_thm
	       THEN
	       `const_comp ( read_cpsr <|proc := 0|> ||| read_scr <|proc := 0|>
			  ||| read_sctlr <|proc := 0|>)` by
	       IMP_RES_TAC parT_const_comp_thm
	       THEN 
	       `const_comp (exc_vector_base <|proc := 0|>
			||| read_cpsr <|proc := 0|> ||| read_scr <|proc := 0|>
													   ||| read_sctlr <|proc := 0|>)` by
	       IMP_RES_TAC parT_const_comp_thm
	       THEN
	       `const_comp (read_reg <|proc := 0|> 15w
			||| exc_vector_base <|proc := 0|>
			    ||| read_cpsr <|proc := 0|> ||| read_scr <|proc := 0|>
																   ||| read_sctlr <|proc := 0|>)`
	       by IMP_RES_TAC parT_const_comp_thm);


     

val const_comp_take_abort_irq_exception_rp_thm = 
    store_thm(
    "const_comp_take_abort_irq_exception_rp_thm", 
    ``const_comp (read_reg <|proc := 0|> 15w ||| exc_vector_base <|proc := 0|>
          ||| have_security_ext <|proc := 0|>
          ||| read_cpsr <|proc := 0|> ||| read_scr <|proc := 0|>
          ||| read_sctlr <|proc := 0|>)``,
    ASSUME_TAC (SPEC ``15w:bool[4]`` read_reg_constlem) 
	       THEN ASSUME_TAC read_cpsr_constlem
	       THEN ASSUME_TAC exc_vector_base_constlem
	       THEN ASSUME_TAC read_scr_constlem
	       THEN ASSUME_TAC have_security_ext_constlem
	       THEN ASSUME_TAC read_sctlr_constlem
	       THEN 
	       `const_comp (read_scr <|proc := 0|>
						||| read_sctlr <|proc := 0|>)` by 
	       IMP_RES_TAC parT_const_comp_thm
	       THEN
	       `const_comp ( read_cpsr <|proc := 0|> ||| read_scr <|proc := 0|>
			  ||| read_sctlr <|proc := 0|>)` by
	       IMP_RES_TAC parT_const_comp_thm
	       THEN 
	       `const_comp (have_security_ext <|proc := 0|> ||| read_cpsr <|proc := 0|>
     ||| read_scr <|proc := 0|> ||| read_sctlr <|proc := 0|>)` by
	       IMP_RES_TAC parT_const_comp_thm
	       THEN
	       `const_comp (exc_vector_base <|proc := 0|>
                           ||| have_security_ext <|proc := 0|> ||| 
                          read_cpsr <|proc := 0|>
                          ||| read_scr <|proc := 0|> ||| read_sctlr <|proc := 0|>)`
	       by IMP_RES_TAC parT_const_comp_thm 
	       THEN METIS_TAC [parT_const_comp_thm]);




val  fixed_undef_svc_exception_rp_thm3 = store_thm(
    "fixed_undef_svc_exception_rp_thm3",
    ``!s H.
          ((s.psrs (0,CPSR)).M = 16w:bool[5] ) ==>
	  (~access_violation s) ==>
	  ((((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> |||
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
           read_sctlr <|proc:=0|>) >>=
				   (\ (a, b, c, d, e). (H:
	    (bool[32]#bool[32]#ARMpsr#CP15scr#CP15sctlr -> unit M)) (a, b, c, d, e))) s)
	= (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> |||
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
           read_sctlr <|proc:=0|>) >>=
				   (\ (a, b, c, d, e). H (
				    get_pc_value s,
				    get_base_vector_table s, 
				    s.psrs (0,CPSR ) with M := 16w ,
				    s.coprocessors.state.cp15.SCR,
				    s.coprocessors.state.cp15.SCTLR))) s))``,
    EVAL_TAC
	THEN RW_TAC (srw_ss())  []
				THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with M:= 16w))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []
 );



val  fixed_abt_irq_exception_rp_thm3 = store_thm(
    "fixed_abt_irq_exception_rp_thm3",
    ``!s H.
          ((s.psrs (0,CPSR)).M = 16w:bool[5] ) ==>
	  (~access_violation s) ==>
	  ((((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> ||| have_security_ext <|proc := 0|> |||
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
           read_sctlr <|proc:=0|>) >>=
				   (\ (a, b, c, d, e,f). (H:
	    (bool[32]#bool[32]#bool#ARMpsr#CP15scr#CP15sctlr -> unit M)) (a, b, c, d, e,f))) s)
	= (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> ||| have_security_ext <|proc := 0|> ||| 
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
           read_sctlr <|proc:=0|>) >>=
				   (\ (a, b, c, d, e,f). H (
				    get_pc_value s,
				    get_base_vector_table s, 
				    get_security_ext s,
				    s.psrs (0,CPSR ) with M := 16w ,
				    s.coprocessors.state.cp15.SCR,
				    s.coprocessors.state.cp15.SCTLR))) s))``,
    EVAL_TAC
	THEN RW_TAC (srw_ss())  []
				THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with M:= 16w))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []
 );


val  fixed_VectorBase_undef_instr_exception_thm1 = store_thm(
    "fixed_VectorBase_undef_instr_exception_thm1",
    ``! e d c b a s.
	  (~access_violation s) ==>
	  (* (Extension_Security ∉ s.information.extensions) ==> *)
	  (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> ||| 
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| 
           read_sctlr <|proc:=0|>) s)
	= ValueState (a, b, c, d, e) s) ==>
	  (b=get_base_vector_table s(* if s.coprocessors.state.cp15.SCTLR.V then *)
	     (* 	 0xFFFF0000w :bool[32] *)
	     (* else *)
	     (* 	 0w  *)
	  )``,
    EVAL_TAC
	THEN RW_TAC (srw_ss())  [] 
					       );

val  fixed_VectorBase_undef_instr_exception_thm2 = store_thm(
    "fixed_VectorBase_undef_instr_exception_thm2",
    ``!s H.
	  (~access_violation s) ==>
	  (* (Extension_Security ∉ s.information.extensions) ==> *)
	  ((((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> ||| 
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| 
           read_sctlr <|proc:=0|>) >>=
				   (\ (a, b, c, d, e). (H:
	    (bool[32]#bool[32]#ARMpsr#CP15scr#CP15sctlr -> unit M)) (a, b, c, d, e))) s)
	= (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> ||| 
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| 
           read_sctlr <|proc:=0|>) >>=
				   (\ (a, b, c, d, e). H (
				    a , 
				    (* if s.coprocessors.state.cp15.SCTLR.V then *)
				    (* 	0xFFFF0000w :bool[32] *)
				    (* else *)
					(get_base_vector_table s) 
				  ,
				    c, 
				    d,
				    e))) s))``,
    EVAL_TAC
	THEN RW_TAC (srw_ss())  [] 
			
 );

val  fixed_VectorBase_abort_irq_exception_thm1 = store_thm(
    "fixed_VectorBase_abort_irq_exception_thm1",
    ``! f e d c b a s.
	  (~access_violation s) ==>
	  (* (Extension_Security ∉ s.information.extensions) ==> *)
	  (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> ||| 
	      have_security_ext <|proc:=0|> ||| 
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| 
           read_sctlr <|proc:=0|>) s)
	= ValueState (a, b, c, d, e,f) s) ==>
	  (b=get_base_vector_table s
	  )``,
    EVAL_TAC
	THEN RW_TAC (srw_ss())  [] 
					       );

val  fixed_VectorBase_abort_irq_exception_thm2 = store_thm(
    "fixed_VectorBase_abort_irq_exception_thm2",
    ``!s H.
	  (~access_violation s) ==>
	  (* (Extension_Security ∉ s.information.extensions) ==> *)
	  ((((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> ||| 
              have_security_ext <|proc:=0|> ||| 
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| 
           read_sctlr <|proc:=0|>) >>=
				   (\ (a, b, c, d, e,f). (H:
	    (bool[32]#bool[32]#bool#ARMpsr#CP15scr#CP15sctlr -> unit M)) (a, b, c, d, e,f))) s)
	= (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> ||| 
	      have_security_ext <|proc:=0|> ||| 
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| 
           read_sctlr <|proc:=0|>) >>=
				   (\ (a, b, c, d, e,f). H (
				    a , 
				    (* if s.coprocessors.state.cp15.SCTLR.V then *)
				    (* 	0xFFFF0000w :bool[32] *)
				    (* else *)
					(get_base_vector_table s) 
				  ,
				    c, 
				    d,
				    e, f))) s))``,
    EVAL_TAC
	THEN RW_TAC (srw_ss())  [] 
			
 );
 				  

val  fixed_sctrl_undef_svc_thm2 = 
     store_thm(
     "fixed_sctrl_undef_svc_thm2",
     ``!s e d c b a. 
	      (~access_violation s) ==>
	      (((read_reg <|proc:=0|> 15w |||
				   exc_vector_base <|proc:=0|> |||  
							    read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) s)
	       = ValueState (a, b, c, d, e) s) ==>
	      (e = s.coprocessors.state.cp15.SCTLR) ``,
     RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def] THEN
	    ASSUME_TAC (SPEC ``15w:bool[4]`` read_reg_constlem) THEN
	    ASSUME_TAC exc_vector_base_constlem THEN
	    ASSUME_TAC read_cpsr_constlem THEN
	    ASSUME_TAC read_scr_constlem 
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN Cases_on `read_reg <|proc:=0|> 15w s` 
	    THEN FULL_SIMP_TAC (srw_ss())  []
	    THEN RES_TAC
	    THEN RW_TAC (srw_ss())  []
	    THEN Cases_on `exc_vector_base <|proc:=0|> b'` 
	    THEN RW_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `read_cpsr <|proc:=0|>  b'` 
	    THEN RW_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `read_scr <|proc:=0|> b'` 
	    THEN RW_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN FULL_SIMP_TAC (srw_ss()) [read_sctlr_def,readT_def]
	    THEN RW_TAC (srw_ss())  []
	    THEN Cases_on `access_violation b'`
	    THEN FULL_SIMP_TAC (srw_ss()) [read_sctlr_def,readT_def]
	    THEN RW_TAC (srw_ss())  []);

			  

val  fixed_sctrl_abt_irq_thm2 = 
     store_thm(
     "fixed_sctrl_abt_irq_thm2",
     ``!s f e d c b a. 
	      (~access_violation s) ==>
	      (((read_reg <|proc:=0|> 15w |||
		 exc_vector_base <|proc:=0|> 
                 ||| have_security_ext <|proc:=0|> |||  
              read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) s)
	       = ValueState (a, b, c, d, e,f) s) ==>
	      (f = s.coprocessors.state.cp15.SCTLR) ``,
     RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def] THEN
	    ASSUME_TAC (SPEC ``15w:bool[4]`` read_reg_constlem) THEN
	    ASSUME_TAC exc_vector_base_constlem THEN
	    ASSUME_TAC read_cpsr_constlem THEN
	    ASSUME_TAC read_scr_constlem THEN
	    ASSUME_TAC have_security_ext_constlem 
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN Cases_on `read_reg <|proc:=0|> 15w s` 
	    THEN FULL_SIMP_TAC (srw_ss())  []
	    THEN RES_TAC
	    THEN RW_TAC (srw_ss())  []
	    THEN Cases_on `exc_vector_base <|proc:=0|> b'` 
	    THEN RW_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `read_cpsr <|proc:=0|>  b'` 
	    THEN RW_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `read_scr <|proc:=0|> b'` 
	    THEN RW_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `have_security_ext <|proc:=0|> b'` 
	    THEN RW_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN FULL_SIMP_TAC (srw_ss()) [read_sctlr_def,readT_def]
	    THEN RW_TAC (srw_ss())  []
	    THEN Cases_on `access_violation b'`
	    THEN FULL_SIMP_TAC (srw_ss()) [read_sctlr_def,readT_def]
	    THEN RW_TAC (srw_ss())  []);



val  fixed_sctrl_undef_svc_thm = store_thm(
		       "fixed_sctrl_undef_svc_thm",
		       ``!s H . 
				((((read_reg <|proc:=0|> 15w |||
				   exc_vector_base <|proc:=0|> |||
				   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| 
				   read_sctlr <|proc:=0|>) >>= (\ (pc,ExcVectorBase,cpsr,scr,sctlr). H (pc,ExcVectorBase,cpsr,scr,sctlr))) s)
				 = 
				 (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> |||
				   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= 
				   (\(pc,ExcVectorBase,cpsr,scr,sctlr). H (pc,ExcVectorBase,cpsr,scr, s.coprocessors.state.cp15.SCTLR))) s))``,
		       MP_TAC (SPEC ``15w:bool[4]`` read_reg_constlem) 
			      THEN MP_TAC read_cpsr_constlem
			      THEN MP_TAC exc_vector_base_constlem
			      THEN MP_TAC read_scr_constlem
			      THEN RW_TAC (srw_ss()) [fixed_sctrl_undef_svc_thm1]
		       );

val fixed_cpsr_undef_svc_thm = 
    store_thm ("fixed_cpsr_undef_svc_thm",
	       ``!s H . 
				((((read_reg <|proc:=0|> 15w |||
				    exc_vector_base <|proc:=0|> |||
				    read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| 
				    read_sctlr <|proc:=0|>) >>= 
                (\ (pc,ExcVectorBase,cpsr,scr,sctlr). H (pc,ExcVectorBase,cpsr,scr,sctlr))) s)
				 = (((read_reg <|proc:=0|> 15w ||| 
				     exc_vector_base <|proc:=0|> |||
				     read_cpsr <|proc:=0|> ||| 
				     read_scr <|proc:=0|> ||| 
				     read_sctlr <|proc:=0|>) >>= 
		(\ (pc,ExcVectorBase,cpsr,scr,sctlr). H (pc,ExcVectorBase,s.psrs (0,CPSR),scr,sctlr))) s))``,
	       MP_TAC (SPEC ``15w:bool[4]`` read_reg_constlem)
		      THEN MP_TAC read_cpsr_constlem
		      THEN MP_TAC exc_vector_base_constlem
		      THEN MP_TAC read_scr_constlem
		      THEN RW_TAC (srw_ss()) [fixed_cpsr_undef_svc_thm1]
		      );


val  fixed_sctrl_abt_irq_thm = store_thm(
		       "fixed_sctrl_abt_irq_thm",
		       ``!s H . 
				((((read_reg <|proc:=0|> 15w |||
				   exc_vector_base <|proc:=0|> |||
                                   have_security_ext <|proc := 0|> |||
				   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| 
				   read_sctlr <|proc:=0|>) >>= (\ (pc,ExcVectorBase,have_security_ext1,cpsr,scr,sctlr). H (pc,ExcVectorBase,have_security_ext1,cpsr,scr,sctlr))) s)
				 = 
				 (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> |||
                                   have_security_ext <|proc := 0|> |||
				   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= 
				   (\(pc,ExcVectorBase,have_security_ext1,cpsr,scr,sctlr). H (pc,ExcVectorBase,have_security_ext1,cpsr,scr, s.coprocessors.state.cp15.SCTLR))) s))``,
		       MP_TAC (SPEC ``15w:bool[4]`` read_reg_constlem) 
			      THEN MP_TAC read_cpsr_constlem
			      THEN MP_TAC exc_vector_base_constlem
			      THEN MP_TAC read_scr_constlem
			      THEN MP_TAC have_security_ext_constlem
			      THEN RW_TAC (srw_ss()) [fixed_sctrl_abt_irq_thm1]
		       );

(******************************************************)
(*******************GENERAL THEOREMS ******************)
(******************************************************)

val hlp_seqT_thm =
store_thm ("hlp_seqT_thm",
			      ``!f g s a s' a'. ((f >>= g) s = ValueState a s') ⇒
			     (f s = ValueState a' s) ⇒
			     ¬access_violation s ⇒
			     (g a' s = ValueState a s')``,
			      RW_TAC (srw_ss()) [seqT_def]
				     THEN FULL_SIMP_TAC (srw_ss()) []
			     );

val hlp_errorT_thm =
store_thm ("hlp_errorT_thm",
				``! g f s e.
			       (f s = Error e) ⇒
			       ((f >>= g) s = Error e)``,
				RW_TAC (srw_ss()) [seqT_def]
				       THEN FULL_SIMP_TAC (srw_ss()) []
			       );

val seqT_access_violation_thm = 
store_thm ("seqT_access_violation_thm", 
	   ``! g f s a s' s'' a'. 
	  ((g >>= f) s = ValueState a s') ⇒
	  (g s = ValueState a' s'') ==>
	  ¬access_violation s' ⇒
	  (¬access_violation s'')``,
	   RW_TAC (srw_ss()) [seqT_def]
		  THEN FULL_SIMP_TAC (srw_ss()) []
		  THEN Cases_on `access_violation s''` 
		  THEN UNDISCH_ALL_TAC
		  THEN RW_TAC (srw_ss()) [seqT_def]
		  THEN FULL_SIMP_TAC (srw_ss()) []
	  );

val parT_access_violation_thm = 
store_thm ("seqT_access_violation_thm", 
	   ``! g f s a s' s'' a'. 
	  ((g ||| f) s = ValueState a s') ⇒
	  (g s = ValueState a' s'') ==>
	  ¬access_violation s' ⇒
	  (¬access_violation s'')
	  ``,
	   RW_TAC (srw_ss()) [seqT_def,parT_def,constT_def]
		  THEN FULL_SIMP_TAC (srw_ss()) []
		  THEN Cases_on `access_violation s''` 
		  THEN UNDISCH_ALL_TAC
		  THEN RW_TAC (srw_ss()) [seqT_def]
		  THEN FULL_SIMP_TAC (srw_ss()) []
	  );


val const_comp_hlp_thm =
    store_thm("const_comp_hlp_thm",
``! f s s' a g. 
	 (const_comp f) ==>
	 (f s = ValueState a s') ==>
     (~access_violation s) ==>
((f >>= g) s = g a s)``
	    ,
	    RW_TAC (srw_ss()) [const_comp_def,seqT_def]
THEN RES_TAC 
THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def,seqT_def]
);

val hlp_seqT2_thm = 
    store_thm ("hlp_seqT2_thm",
    ``!f g s a s' b s1 e. ((f >>= g) s = ValueState a s') ==>
	      ((f s = ValueState b s1) ==>
	      (~access_violation s1) ==>
	      (g b s1 = ValueState a s'))
    /\ ~(f s = Error e)
``,
RW_TAC (srw_ss()) [seqT_def]
THEN Cases_on `f s`
THEN FULL_SIMP_TAC (srw_ss()) [seqT_def]
);

val hlp_seqT3_thm = 
    store_thm ("hlp_seqT3_thm",
    ``!g f s e. 
	      (f s = Error e) ==>
	      ((f >>= g) s = Error e)
``,
RW_TAC (srw_ss()) [seqT_def]
);


val hlp_seqT4_thm = 
    store_thm ("hlp_seqT4_thm",
	       ``!f H s1 s2 s1' s2' a1 g invr1 invr2 uf uy. 
              (~access_violation s1') ==>
	      (~access_violation s2') ==>
	      (f s1 = ValueState a1 s1') ==>
	      (f s2 = ValueState a1 s2') ==>
	      (preserve_relation_mmu_abs H invr1 invr2 uf uy) ==>
              (mmu_requirements s1' g) ⇒
              (mmu_requirements s2' g) ⇒
              (similar g s1' s2') ⇒
              (uy g s1' s2' )⇒
              (invr1 s1' )⇒
              (invr1 s2' )⇒
	      ((?a s1'' s2''. ((f >>= H) s1 = ValueState a s1'') 
		/\
		     ((f >>= H) s2 = ValueState a s2''))
			     \/
	      (?e .((f >>= H) s1 = Error e) 
	       /\
		    ((f >>= H) s2 = Error e)))
              
	      ``,
	       RW_TAC (srw_ss()) [preserve_relation_mmu_abs_def,seqT_def]
		      THEN RES_TAC
		      THEN PAT_ASSUM ``!c. X`` (fn thm => ASSUME_TAC (SPEC ``a1:'a`` thm))
		      THEN FULL_SIMP_TAC (srw_ss()) [seqT_def]
	      );

val similar_states_have_same_pc_thm = 
    store_thm ("similar_states_have_equal_pc_thm",
	       ``! s1 s2 g. 
	      similar g s1 s2 ==>
	      (s2.registers (0,RName_PC)=
	       s1.registers (0,RName_PC))``,
	       RW_TAC (srw_ss()) [similar_def,equal_user_register_def]
	      );

val similar_states_have_same_cpsr_thm = 
    store_thm ("similar_states_have_equal_cpsr_thm",
	       ``! s1 s2 g. 
	      similar g s1 s2 ==>
	      (s2.psrs (0,CPSR)=
	       s1.psrs (0,CPSR))``,
	       RW_TAC (srw_ss()) [similar_def,equal_user_register_def]
	      );
val similar_states_have_same_mode_thm = 
    store_thm ("similar_states_have_same_av_thm1",
	       ``! u s1 s2 g. 
	      similar g s1 s2 ==>
	      ((s2.psrs (0,CPSR)).M = u) ⇒
       ((s1.psrs (0,CPSR)).M = u)``,
	       RW_TAC (srw_ss()) [similar_def]
	      );

val similar_states_have_same_mode_thm = 
    store_thm ("similar_states_have_same_av_thm1",
	       ``! u s1 s2 g. 
	      similar g s1 s2 ==>
	      ((s2.psrs (0,CPSR)).M = u) ⇒
       ((s1.psrs (0,CPSR)).M = u)``,
	       RW_TAC (srw_ss()) [similar_def]
	      );

val similar_states_have_same_av_thm1 = 
    store_thm ("similar_states_have_same_av_thm1",
	       ``! s1 s2 g. 
	      similar g s1 s2 ==>
	      (
	       ((~access_violation s2) ==>
	      (~access_violation s1))
	       /\
		    ((~access_violation s1) ==>
		    (~access_violation s2)))
	      ``,
	       RW_TAC (srw_ss()) [similar_def]
	      );

val similar_states_have_same_vec_tab_thm = 
    store_thm ("similar_states_have_same_vec_tab_thm",
	       ``! s1 s2 g. 
	      similar g s1 s2 ==>
	      (
	       get_base_vector_table s1 =
	       get_base_vector_table s2) 
	      ``,
	       RW_TAC (srw_ss()) [similar_def, get_base_vector_table_def]
	      );


val similar_states_have_same_security_ext_thm = 
    store_thm ("similar_states_have_same_security_ext_thm",
	       ``! s1 s2 g. 
	      similar g s1 s2 ==>
	      (
	       get_security_ext s1 =
	       get_security_ext s2) 
	      ``,
	       RW_TAC (srw_ss()) [similar_def, get_security_ext_def]
	      );

val similar_states_have_same_read_pc_thm = 
    store_thm ("similar_states_have_same_read_pc_thm",
	       ``! s1 s2 g. 
	      similar g s1 s2 ==>
	      (
	       get_pc_value s1 =
	       get_pc_value s2) 
	      ``,
	       RW_TAC (srw_ss()) [similar_def, get_pc_value_def,equal_user_register_def]
			     THEN UNABBREV_ALL_TAC
			     THEN EVAL_TAC
			     THEN RW_TAC (srw_ss()) []
	      );

val similar_states_have_same_av_thm2 = 
    store_thm ("similar_states_have_same_av_thm2",
	       ``! s1 s2 g. 
	        similar g s1 s2 ==>
	      (
	       ((access_violation s2) ==>
	      (access_violation s1))
	       /\
		    ((access_violation s1) ==>
		    (access_violation s2)))``,
	       RW_TAC (srw_ss()) [similar_def]
	      );

val untouched_states_implies_mmu_setup_thm = 
    store_thm ("untouched_states_implies_mmu_setup",
	       ``! s1 t g. 
	      untouched g s1 t ==>
	      ((s1.coprocessors.state.cp15.C1 =
          t.coprocessors.state.cp15.C1) /\
         (s1.coprocessors.state.cp15.C2 =
          t.coprocessors.state.cp15.C2) /\
         (s1.coprocessors.state.cp15.C3 =
          t.coprocessors.state.cp15.C3))``,
	       RW_TAC (srw_ss()) [untouched_def]
	      );


val satisfy_priv_constraints_v3_def = 
Define `satisfy_priv_constraints_v3 f m n =
 !g s1 s1' a .   
     mmu_requirements s1 g ⇒
     (* (Extension_Security ∉ s1.information.extensions) ==> *)
     (ARM_MODE s1 = m) ==>
     (ARM_MODE s1' = n) ==>
     (f s1 = ValueState a s1') ==>
     (¬access_violation s1) ==>
     (¬access_violation s1') ==>
     priv_mode_constraints_v3 g s1 s1'`;

val satisfy_priv_constraints_v2_def = 
Define `satisfy_priv_constraints_v2 f m n =
 !g s1 s1' a .   
     mmu_requirements s1 g ⇒
     (* (Extension_Security ∉ s1.information.extensions) ==> *)
     (ARM_MODE s1 = m) ==>
     (ARM_MODE s1' = n) ==>
     (f s1 = ValueState a s1') ==>
     (¬access_violation s1) ==>
     (¬access_violation s1') ==>
     priv_mode_constraints_v2 g s1 s1'`;

(************                       **********************)
(*********to be proved or borrowed from oliver ***********)

val  fixed_cpsr_abt_irq_thm = new_axiom(
		       "fixed_cpsr_abt_irq_thm",
		       ``!s H . 
				((((read_reg <|proc:=0|> 15w |||
				    exc_vector_base <|proc:=0|> ||| 
                                    have_security_ext <|proc := 0|> |||
				    read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| 
				    read_sctlr <|proc:=0|>) >>= 
                (\ (pc,ExcVectorBase,have_security_ext1,cpsr,scr,sctlr). 
                 H (pc,ExcVectorBase,have_security_ext1,cpsr,scr,sctlr))) s)
				 = (((read_reg <|proc:=0|> 15w ||| 
				     exc_vector_base <|proc:=0|> ||| 
                                     have_security_ext <|proc := 0|> |||
				     read_cpsr <|proc:=0|> ||| 
				     read_scr <|proc:=0|> ||| 
				     read_sctlr <|proc:=0|>) >>= 
		(\ (pc,ExcVectorBase,have_security_ext1,cpsr,scr,sctlr). 
                 H (pc,ExcVectorBase,have_security_ext1,s.psrs (0,CPSR),scr,sctlr))) s))``);


val  fixed_cpsr_undef_svc_thm2 = 	
     new_axiom("fixed_cpsr_undef_svc_thm2",
			``!s a b c d e. 
				 (~access_violation s) ==>
				 (((read_reg <|proc:=0|> 15w |||
				    exc_vector_base <|proc:=0|> ||| 
				    read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) s)
				  = ValueState (a, b, c, d, e) s) ==>
				 (c = s.psrs (0,CPSR)) ``);

val  fixed_cpsr_abt_irq_thm2 = 	
     new_axiom("fixed_cpsr_abt_irq_thm2",
	       ``!s a b c d e f. 
	      (~access_violation s) ==>
	      (((read_reg <|proc := 0|> 15w ||| exc_vector_base <|proc := 0|>
                ||| have_security_ext <|proc := 0|> ||| read_cpsr <|proc := 0|>
                ||| read_scr <|proc := 0|> ||| read_sctlr <|proc := 0|>) s)
				  = ValueState (a, b, c, d, e ,f) s) ==>
				 (d = s.psrs (0,CPSR)) ``);

val  fixed_pc_undef_svc_thm2 = 	
     new_axiom("fixed_pc_undef_svc_thm2",
	       ``!s a b c d e. 
	      (~access_violation s) ==>
	      (((read_reg <|proc:=0|> 15w |||
				   exc_vector_base <|proc:=0|> ||| 
				    read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) s)
				  = ValueState (a, b, c, d, e) s) ==>
				 (a = get_pc_value s)``);

val  fixed_pc_abt_irq_thm2 = 	
     new_axiom("fixed_pc_abt_irq_thm2",
	       ``!s a b c d e f. 
	      (~access_violation s) ==>
	      (((read_reg <|proc:=0|> 15w |||
				   exc_vector_base <|proc:=0|>
||| have_security_ext <|proc := 0|> ||| 
				    read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) s)
				  = ValueState (a, b, c, d, e,f) s) ==>
				 (a = get_pc_value s)``);



(***********************************************************)


val IT_advance_untouch_mmu_setup_thm = 
    store_thm ("IT_advance_untouch_mmu_setup_thm",
	       ``!s a s'.
	      (IT_advance <|proc := 0|> s = ValueState a s') ==>
	      ((s.coprocessors = s'.coprocessors)
	       /\
	    (s.memory = s'.memory)
	       /\
		    (s.accesses = s'.accesses))
	      ``
	     ,
	     EVAL_TAC
		 THEN RW_TAC (srw_ss()) []
		 THEN UNDISCH_ALL_TAC
		 THEN (NTAC 2 (RW_TAC (srw_ss()) []))
);


val IT_advance_kepp_access_violation_thm = 
    store_thm ("IT_advance_kepp_access_violation_thm",
	       ``!s a s' g. mmu_requirements s g ==>
	      ¬access_violation s ==>
	      (* Extension_Security ∉ s.information.extensions ==> *)
	      (IT_advance <|proc := 0|> s = ValueState a s') ==>
	      ¬access_violation s'``
	     ,
	     RW_TAC (srw_ss()) [seqT_def]
		    THEN IMP_RES_TAC IT_advance_untouch_mmu_setup_thm
		    THEN IMP_RES_TAC (SPECL [``s:arm_state``, 
					     ``s':arm_state``, 
					     ``g:bool[32]``] 
					    trivially_untouched_av_lem2)
		    THEN UNDISCH_ALL_TAC
		    THEN RW_TAC (srw_ss()) []
	      );




val IT_advance_untouch_security_ex_thm = 
    store_thm ("IT_advance_untouch_security_ex_thm",
	       ``!y s.
	      Extension_Security ∉ s.information.extensions ==>
	        (IT_advance <|proc := 0|> s = ValueState a s') ==>
	    Extension_Security ∉ s'.information.extensions 

	      ``
	     ,
	    EVAL_TAC
		 THEN RW_TAC (srw_ss()) []
		 THEN UNDISCH_ALL_TAC
		 THEN (NTAC 2 (RW_TAC (srw_ss()) []))
);

(* val IT_advance_untouch_security_ex_thm =  *)
(*     store_thm ("IT_advance_untouch_security_ex_thm", *)
(* 	       ``!y s. *)
(* 	       (¬access_violation s) ==> *)
(* 	       (¬access_violation s') ==> *)
(* 	       ((current_instr_set <|current_instr_setproc := 0|> s) = ValueState is s )==> *)
(* 	        (IT_advance <|proc := 0|> s = ValueState a s') ==> *)
(* 	    ((current_instr_set <|proc := 0|> s') = (ValueState is s') ) *)
	     
(* 	      `` *)
(* 	     , *)
(* 	    EVAL_TAC *)
(* 		 THEN RW_TAC (srw_ss()) [] *)(* 		 THEN UNDISCH_ALL_TAC *)
(* 		 THEN ((* NTAC 2 *) (RW_TAC (srw_ss()) [])) *)
(* ); *)




