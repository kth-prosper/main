
val reflex_priv_mode_constraints_v1_thm = 
store_thm("reflex_priv_mode_constraints_v1_thm",
``reflexive_comp   priv_mode_constraints_v1 (assert_mode 16w)``
, RW_TAC (srw_ss()) [ reflexive_comp_def,priv_mode_constraints_v1_def,assert_mode_def]);

val trans_priv_mode_constraints_v1_thm = 
    save_thm("trans_priv_mode_constraints_v1_thm",
	      new_axiom ("trans_priv_mode_constraints_v1_thm_X",``trans_fun priv_mode_constraints_v1``));


val uy1 = ``priv_mode_similar``;
val uf1 = ``priv_mode_constraints_v1``;

val errorT_thm = 
    store_thm("errorT_thm",
	      ``! inv s uf1 uy1. preserve_relation_mmu (errorT s) inv inv uf1 uy1 ``,
	      (RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def,
				  assert_mode_def,errorT_def,untouched_def]));

val errorT_comb_thm = 
    store_thm("errorT_comb_thm",
	      ``! inv1 inv2 s uf1 uy1. preserve_relation_mmu (errorT s) inv1 inv2 uf1 uy1 ``,
	      (RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def,
				  assert_mode_def,errorT_def,untouched_def]));

val arch_version_thm =
   save_thm("arch_version_thm",
	   new_axiom("arch_version_thmX", ``! m n k . preserve_relation_mmu (arch_version ii) 
	      (assert_mode n) (assert_mode  n) ^uf1 ^uy1``));


val read_info_thm = 
   save_thm("read_info_thm",
	   new_axiom("read_info_thm_X",
``preserve_relation_mmu (read_info <|proc := 0|>) (assert_mode 16w)
       (assert_mode 16w) priv_mode_constraints_v1 priv_mode_similar``));



val read_cpsr_thm = store_thm("read_cpsr_thm",
  `` preserve_relation_mmu (read_cpsr <|proc := 0|>) (assert_mode 16w) (assert_mode 16w) ^uf1 ^uy1``,
 (RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def, assert_mode_def,read_cpsr_def,read__psr_def,readT_def,untouched_def,priv_mode_constraints_v1_def]
THEN (RW_TAC (srw_ss()) [] )));


val write_cpsr_thm =
   save_thm("write_cpsr_thm",
	   new_axiom("write_cpsr_thmX",
`` !u' u.  preserve_relation_mmu ( write_cpsr <|proc :=0 |> (cpsr with M := u)) 
		(assert_mode u') (assert_mode u) ^uf1 ^uy1 ``));

val write_cpsr_comb_thm =
   save_thm("write_cpsr_thm",
	   new_axiom("write_cpsr_thmX",
`` !u' u.  preserve_relation_mmu ( write_cpsr <|proc :=0 |> (cpsr with M := u)) 
		(assert_mode u') (assert_mode u) ^uf1 ^uy1``));


val take_undef_instr_exception_thm =
   save_thm("take_undef_instr_exception_thm",
	   new_axiom("take_undef_instr_exception_thmX",
``preserve_relation_mmu (take_undef_instr_exception <|proc := 0|>)
  (assert_mode 16w) (comb_mode 16w 27w) ^uf1 ^uy1``));

val take_undef_instr_exception_comb_thm =
   save_thm("take_undef_instr_exception_comb_thm",
	   new_axiom("take_undef_instr_exception_comb_thmX",
``preserve_relation_mmu (take_undef_instr_exception <|proc := 0|>)
  (assert_mode 16w) (comb_mode 16w 27w) ^uf1 ^uy1``));


val read__reg_thm = 
    save_thm ("read__reg_thm",
	   new_axiom("read__reg_thmX",
``preserve_relation_mmu  (read__reg <|proc := 0|> rname)
  (assert_mode 16w) (assert_mode 16w) ^uf1 ^uy1``));

val write__reg_thm = 
    save_thm ("write__reg_thm",
	   new_axiom("write__reg_thmX",
``preserve_relation_mmu  (write__reg <|proc := 0|> value rname)
  (assert_mode 16w) (assert_mode 16w) ^uf1 ^uy1``));

val address_mode2_thm = save_thm("address_mode2_thm",
                        new_axiom("address_mode2_thmX",
                        ``preserve_relation_mmu  (address_mode2 ii indx add base m2) (assert_mode u) (assert_mode u) ^uf1 ^uy1``));

val read_memU_with_priv_thm = save_thm("read_memU_with_priv_thm",
                        new_axiom("read_memU_with_priv_thmX",
                        ``preserve_relation_mmu  (read_memU_with_priv (ii:iiid) (address:word32, size:num, privileged:bool)) (assert_mode u) (assert_mode u) ^uf1 ^uy1``)); (* for loop *)


val write_isetstate_thm =
   save_thm("write_isetstate_thm",
	   new_axiom("write_isetstate_thmX",
``!k. preserve_relation_mmu  (write_isetstate  <|proc := 0|> k)
		    (assert_mode 16w) (assert_mode 16w) ^uf1 ^uy1``));

val read_isetstate_thm =
   save_thm("read_isetstate_thm",
	   new_axiom("read_isetstate_thmX",
``preserve_relation_mmu  (read_isetstate  <|proc := 0|> )
		    (assert_mode 16w) (assert_mode 16w) ^uf1 ^uy1``));

val current_instr_set_thm =
   save_thm("current_instr_set_thm",
	   new_axiom("current_instr_set_thmX",
``preserve_relation_mmu (current_instr_set <|proc := 0|>)
       (assert_mode 16w) (assert_mode 16w) priv_mode_constraints_v1
       priv_mode_similar``));


val write_cpsr_IT_thm =
   save_thm("write_cpsr_IT_thm",
	   new_axiom("write_cpsr_IT_thmX",
``preserve_relation_mmu (write_cpsr <|proc := 0|> (cpsr with IT := 0w))
		    (assert_mode 16w) (assert_mode 16w) ^uf1 ^uy1``));



val a = ``if toARM ∧ (CurrentInstrSet = InstrSet_ThumbEE) then
             take_undef_instr_exception <|proc:=0|>
           else
	      read_reg <|proc:=0|> 15w >>=
                (λpc.
                   (if CurrentInstrSet = InstrSet_ARM then
                      write_reg <|proc:=0|> 14w (pc − 4w)
                    else
                      write_reg <|proc:=0|> 14w ((0 :+ T) pc)) >>=
                   (λu.
                      (let targetAddress =
                             if targetInstrSet = InstrSet_ARM then
                               align (pc,4) + imm32
                             else
                               pc + imm32
                       in
                         
                         (branch_write_pc <|proc:=0|> targetAddress))))``;

val a = `` divide_instr <|proc:=0|> (Divide unsigned n d m)``;

val () = global_mode := ``16w:bool[5]``;
val src_inv = ``(assert_mode 16w)``;
val trg_inv =  ``comb_mode 16w 27w``;
val uargs = [uf1,uy1,``27w:bool[5]``,``_thm``];
val pthms = [trans_priv_mode_constraints_v1_thm,
	     reflex_priv_mode_constraints_v1_thm,
	     priv_mode_similar_def,
	     priv_mode_constraints_v1_def];

prove a src_inv trg_inv uargs pthms;


























(* val uy2 = ``priv_mode_similar``; *)
(* val uf2 = ``priv_mode_constraints_v1``; *)
(* val uf2 = ``tautology_fun``; *)
(* val () = global_mode := ``27w:bool[5]``; *)
(* val trg_inv = ``(assert_mode 27w)``; *)






























val a = ``load_instr <|proc:=0|> enc (Load indx add load_byte w unpriv n t mode2)``;
val a = ``(read_cpsr <|proc:=0|>)``;
val a = ``((* read_cpsr <|proc:=0|> >>= *)
		     ((* λcpsr. *)
		      if (cpsr.IT = 0w) ∨ cpsr.T then
			 errorT "IT_advance: unpredictable"
		      else
			   have_security_ext <|proc:=0|>))``;


val a = ``(if p then
           errorT "if_then: unpredictable"
         else if
           (mask = 0w)  (firstcond = 15w)
           (firstcond = 14w)  bit_count mask  1
         then
          take_undef_instr_exception <|proc := 0|>
          else
           (read_cpsr <|proc := 0|> >>=
            (cpsr.
               (increment_pc <|proc := 0|> Encoding_Thumb
                  ||| write_cpsr <|proc := 0|>
                        (cpsr with IT := firstcond @@ mask)) >>=
               ((u1,u2). return ()))))``;

	      












val a = ``take_undef_instr_exception <|proc :=0|>``;
val a = ``(λ(u1,u2).
         (write_spsr <|proc := 0|> (cpsr with M := 16w)
            ||| write_reg <|proc := 0|> 14w
                  (if cpsr.T then
                     pc + 0xFFFFFFFEw
                   else
                     pc + 0xFFFFFFFCw)
            ||| read_cpsr <|proc := 0|> >>=
                (λcpsr.
                   write_cpsr <|proc := 0|>
                     (cpsr with
                      <|IT := 0w; J := F; E := sctlr.EE; I := T;
                        T := sctlr.TE|>))
            ||| branch_to <|proc := 0|> (ExcVectorBase + 4w)) >>=
         (λ(u1,u2,u3,u4). return ()))``;

val a = ``(read_cpsr <|proc := 0|> >>=
      (λcpsr. write_reg_mode <|proc := 0|> (14w,27w) value))``;

val pthms = [trans_have_same_mem_accesses_thm,
	     reflex_have_same_mem_accesses_thm,
	     tautology_fun_def,
	     have_same_mem_accesses_def,
	     read_write_cpsr_thm
(*write_scr_cpsr_thm*)];
val () = global_mode := ``27w:bool[5]``;
prove a ``(assert_mode 27w)`` ``(assert_mode 27w)`` uargs pthms;


val () = global_mode := ``16w:bool[5]``;
val a = `` divide_instr <|proc:=0|> (Divide unsigned n d m)``;
val (_) =     prove a src_inv trg_inv uargs;




val (a_abs,a_body) = pairLib.dest_pabs a;
val  _ = (set_goal([], `` 
		  preserve_relation_mmu ^a_body ^src_inv ^trg_inv ^uf2 ^uy2``));	
val (flag,l ,r , opr) = decompose a src_inv trg_inv;

g `preserve_relation_mmu ^a ^src_inv ^trg_inv ^uf2 ^uf2`;	

val a = ``take_fiq_exception  <|proc:=0|>``;
val (thm, tac) =    prove a src_inv trg_inv ``17w:bool[5]`` uargs;
	



(* example of using tool for proving branch_pc *)

val a = ``((read_reg <|proc := 0|> 15w
               ||| exc_vector_base <|proc := 0|>
               ||| read_cpsr <|proc := 0|> ||| read_scr <|proc := 0|>
               ||| read_sctlr <|proc := 0|>) >>=
            (λ(a,b,c,d,e).
               (condT (c.M = 22w)
                  (write_scr <|proc := 0|> (d with NS := F))
                  ||| write_cpsr <|proc := 0|> (c with M := 27w)) >>=
               (λ(u1,u2).
                  (write_spsr <|proc := 0|> c
                     ||| write_reg <|proc := 0|> 14w
                           (if c.T then
                              a + 0xFFFFFFFEw
                            else
                              a + 0xFFFFFFFCw)
                     ||| read_cpsr <|proc := 0|> >>=
                         (λcpsr.
                            write_cpsr <|proc := 0|>
                              (cpsr with
                               <|IT := 0w; J := F; E := e.EE; I := T;
                                 T := e.TE|>))
                     ||| branch_to <|proc := 0|> 4w))))``


val expr = ``(4w:bool[32])``;
val cm = ``(27w:bool[5])``;
val thms = [set_pc_to_def,
	    seqT_set_pc_to_thm,
	    parT_set_pc_to_thm,
	    pc_first_abs_lemma,
	    pc_second_abs_lemma,
	    base_pfc_thm
	   ];

val postfix = "_pc_thm";
val _ = proofManagerLib.b()
val a' = get_action_from_goal (top_goal());
val (flag,l ,r , opr) = decompose a' postfix;
prove_const  a ``set_pc_to`` ``(4w:bool[32])`` ``(27w:bool[5])`` "_switch_pc_thm" thms;



(******************* SCTRL.EE *****************)
g `(take_undef_instr_exception <| proc:=0 |> s = ValueState a s') ==>
 ((s'.psrs (ii.proc, CPSR)).E = 
    (s.coprocessors.state.cp15.SCTLR.EE))`;

RW_TAC (srw_ss()) [take_undef_instr_exception_def]
val a = ``(λ(pc,ExcVectorBase,cpsr,scr,sctlr).
      (condT (cpsr.M = 22w) (write_scr <|proc := 0|> (scr with NS := F))
         ||| write_cpsr <|proc := 0|> (cpsr with M := 27w)) >>=
      (λ(u1,u2).
         ((* write_spsr <|proc := 0|> cpsr *)
          (*   ||| *) write_reg <|proc := 0|> 14w
                  (if cpsr.T then
                     pc + 0xFFFFFFFEw
                   else
                     pc + 0xFFFFFFFCw)
            ||| read_cpsr <|proc := 0|> >>=
                (λcpsr.
                   write_cpsr <|proc := 0|>
                     (cpsr with
                      <|IT := 0w; J := F; E := sctlr.EE; I := T;
                        T := sctlr.TE|>))
            ||| branch_to <|proc := 0|> (ExcVectorBase + 4w)) >>=
         (λ(u1,u2,u3(* ,u4 *)). return ()))):(word32 # word32 # ARMpsr # CP15scr # CP15sctlr -> unit M)``;

ASSUME_TAC (SPECL [``s:arm_state``,h] 
		  (INST_TYPE [alpha |-> ``:unit``] fixed_sctrl_thm))

FULL_SIMP_TAC (srw_ss()) []











(*****************************************************)


g `(const_comp f) ==>
	(const_comp g) ==>
		(const_comp (f ||| g))`;

RW_TAC (srw_ss())  [const_comp_def,seqT_def,parT_def,constT_def]
Cases_on `f s`
FULL_SIMP_TAC (srw_ss())  []
RES_TAC
Cases_on `access_violation b`
FULL_SIMP_TAC (srw_ss())  []
Cases_on `g b`
FULL_SIMP_TAC (srw_ss())  []
RES_TAC
Cases_on `access_violation b'`
FULL_SIMP_TAC (srw_ss())  [];








SIMP_CONV (srw_ss()) [align_def] (concl thm); 
SIMP_RULE (srw_ss()) [align_def] (thm); 








val take_undef_instr_exception_pfc_thm = store_thm ("take_undef_instr_exception_pfc_thm",
``!s a s'. (¬access_violation s)==>
   preserve_relation_mmu (take_undef_instr_exception <|proc:=0|>) (assert_mode 16w) (assert_mode 27w) tatulogy_fun tatulogy_fun``,

val a = SIMP_CONV (bool_ss) [take_undef_instr_exception_def] 
				     ``take_undef_instr_exception <|proc:=0|> ``;
		   val (_, a') =  (dest_eq (concl a))
		   val (l,r,rb1)= decompose_term a' 
		   val (a_abs,a_body) = pairLib.dest_pabs r;
	

FULL_SIMP_TAC (bool_ss) [take_undef_instr_exception_def] 
THEN RW_TAC (srw_ss()) [(SIMP_RULE (srw_ss()) [] (SPECL [``15w:bool[4]``,
			 r, ``assert_mode 27w``, ``tatulogy_fun``,
			 ``tatulogy_fun``] 
			(INST_TYPE [alpha |-> ``:unit``] 
				   cpsr_quintuple_simp_rel_lem2))) ]


THEN
ASSUME_TAC (SPECL [``s:arm_state``,r] 
	  (INST_TYPE [alpha |-> ``:unit``] fixed_sctrl_thm)) THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
POP_ASSUM (fn thm => THROW_AWAY_TAC (concl thm))  THEN
ASSUME_TAC const_comp_take_exception_reading_part_thm THEN
RW_TAC (srw_ss()) [priv_flags_constraints_def,priv_flags_constraints_abs_def]
THEN NTAC 4
( FULL_SIMP_TAC (srw_ss()) [const_comp_def]
THEN Cases_on [QUOTE ("("^(term_to_string l) ^ ") s'")]

THENL
[ RES_TAC 
THEN RW_TAC (srw_ss()) []
THEN IMP_RES_TAC hlp_seqT_thm
THEN PAT_ASSUM ``X a' b= ValueState a s'`` (fn thm => ASSUME_TAC (PairRules.PBETA_RULE thm))
THEN ASSUME_TAC ( SPECL 
		  [``(SND (SND (SND (SND (a:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr)))))):CP15sctlr``,
		   ``(FST (SND (SND (SND (a:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr)))))):CP15scr``,
		   ``(FST (a:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr))):word32``,
		   ``(FST (SND (SND (a:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr))))):ARMpsr``,
		   ``(FST (SND (a:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr)))):word32``,
		   ``b:arm_state``,
		   ``s'':arm_state``,
		   ``():unit``
		  ]  (GEN_ALL  (SIMP_RULE (bool_ss) [priv_flags_constraints_def] thm5)))
THEN PAT_ASSUM ``X ==> Y`` (fn thm => ASSUME_TAC (PairRules.PBETA_RULE thm))
THEN ASSUME_TAC (SPECL [``b:arm_state``,
	``(FST (a:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr))):word32``,
	``(FST (SND (a:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr)))):word32``, 
	``(FST (SND (SND (a:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr))))):ARMpsr``,
	``(FST (SND (SND (SND (a:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr)))))):CP15scr``,
	``(SND (SND (SND (SND (a:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr)))))):CP15sctlr``] fixed_sctrl_thm2)
THEN RES_TAC 
THEN FULL_SIMP_TAC (srw_ss()) [],

IMP_RES_TAC (SPEC r (INST_TYPE [beta |-> ``:unit``,
				     alpha |-> ``:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr)`` ] hlp_errorT_thm))
THEN 
 PAT_ASSUM ``! (s''':arm_state). X `` (fn thm => ASSUME_TAC (SPEC ``s':arm_state``thm))
THEN
RW_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [] ]));
