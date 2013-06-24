
fun gen_user_reg_names (i:string) =
    let val user_reg_names =
            [mk_var("cr0"^i,``:word32``)   , mk_var("cr1"^i,``:word32``)       ,
	     mk_var("cr2"^i,``:word32``)    , mk_var("cr3"^i,``:word32``)	   ,	 
	     mk_var("cr4"^i,``:word32``)    , mk_var("cr5"^i,``:word32``)	   ,
	     mk_var("cr6"^i,``:word32``)    , mk_var("cr7"^i,``:word32``)	   ,
	     mk_var("cr8"^i,``:word32``)    , 
	     mk_var("cr9"^i,``:word32``)    , 
	     mk_var("cr10"^i,``:word32``)   , 
	     mk_var("cr11"^i,``:word32``)   , 
	     mk_var("cr12"^i,``:word32``)   , 
	     mk_var("csp"^i,``:word32``)    , mk_var("clr"^i,``:word32``)	   ,
	     mk_var("cpc"^i,``:word32``)] in
	listSyntax.mk_list (user_reg_names , ``:word32``)
    end; 
    
	      
val mk_user_regs_def = 
    Define ` mk_user_regs rv = 
	     RName_User_case  ((EL 0 rv):bool[32])
			      (EL 1 rv)
			      (EL 2 rv)
			      (EL 3 rv)
			      (EL 4 rv) 
			      (EL 5 rv) 
			      (EL 6 rv) 
			      (EL 7 rv) 
			      (EL 8 rv) 
			      (EL 9 rv) 
			      (EL 10 rv) 
			      (EL 11 rv)  
			      (EL 12 rv)  
			      (EL 13 rv)  
			      (EL 14 rv)  
			      (EL 15 rv) `;

fun gen_psr_names (i:string) =
    let val psr_names =
            [mk_var("N"^i,``:bool``)    , mk_var("Z"^i,``:bool``)  ,
	     mk_var("C"^i,``:bool``)    , mk_var("rV"^i,``:bool``) ,	 
	     mk_var("Q"^i,``:bool``)    , mk_var("J"^i,``:bool``)  ,
	     mk_var("E"^i,``:bool``)    , mk_var("A"^i,``:bool``)  ,
	     mk_var("I"^i,``:bool``)    , mk_var("F"^i,``:bool``)  ,
	     mk_var("T"^i,``:bool``)] in
	listSyntax.mk_list (psr_names , ``:bool``)
	
    end;

val mk_psrs_def = 
    Define ` mk_psrs rv it1 ge1 res1 m= 
	<|
	N := (EL 0 rv); Z := (EL 1 rv); C := (EL 2 rv); V := (EL 3 rv);
	Q := (EL 4 rv); IT := it1;
	J := (EL 5 rv); Reserved := res1;
	GE := ge1; E := (EL 6 rv); A := (EL 7 rv);
	I := (EL 8 rv); F := (EL 9 rv); T := (EL 10 rv); M := m
						  |>`;

    
fun mk_context i =
    let val user_regs = gen_user_reg_names i 
	val (psr_list , it1, ge,res, m) = 
	    (gen_psr_names i, mk_var("it"^i,``:bool[8]``),
	     mk_var("ge"^i,``:bool[4]``),
	     mk_var("res"^i,``:bool[4]``), mk_var("m"^i,``:bool[5]``)) 
	val cpsr = ``(mk_psrs ^psr_list ^it1 ^ge ^res ^m)``;
	val context = EVAL ``<| registers := (mk_user_regs ^user_regs);
             spsr := ^cpsr |>``
	val (_, post) = dest_thm context
	val (_, context) = dest_eq post
    in context
    end;


fun mk_log_comp i id =
    let  val context1 = mk_context ("c1"^i); 
	 val context2 = mk_context ("c2"^i);
	 (* val guest= mk_var("guest"^i,``:bool[32]``); *)
	 val msg1= mk_var("msg1"^i,``:bool[32]``);
	 val flg1= mk_var("flg1"^i,``:bool``);      
	 val msg2= mk_var("msg2"^i,``:bool[32]``);
	 val flg2= mk_var("flg2"^i,``:bool``); 
	 val rdy1= mk_var("rdy1"^i,``:bool``); 
	 val rdy2= mk_var("rdy2"^i,``:bool``);    
	 val log_comp =	 
             `` <| 
	     active_machine  := ^id  ;
             message_box1    := ^msg1;
             box_full1       := ^flg1;
             message_box2    := ^msg2;
             box_full2       := ^flg2;
             context1        := (^context1);
             context2        := (^context2);
             ready1          := ^rdy1;
             ready2          := ^rdy2 
				     |>``;
    in log_comp
    end;


fun gen_reg_names (i:string) =
    let val reg_names =
            [mk_var("r0"^i,``:word32``)    , mk_var("r1"^i,``:word32``)            ,
	     mk_var("r2"^i,``:word32``)    , mk_var("r3"^i,``:word32``)	           ,	 
	     mk_var("r4"^i,``:word32``)    , mk_var("r5"^i,``:word32``)	           ,
	     mk_var("r6"^i,``:word32``)    , mk_var("r7"^i,``:word32``)	           ,
	     mk_var("r8"^i,``:word32``)    , mk_var("r8_fiq"^i,``:word32``)	   ,
	     mk_var("r9"^i,``:word32``)    , mk_var("r9_fiq"^i,``:word32``)	   ,
	     mk_var("r10"^i,``:word32``)   , mk_var("r10_fiq"^i,``:word32``)	   ,
	     mk_var("r11"^i,``:word32``)   , mk_var("r11_fiq"^i,``:word32``)	   ,
	     mk_var("r12"^i,``:word32``)   , mk_var("r12_fiq"^i,``:word32``)	   ,
	     mk_var("sp"^i,``:word32``)    , mk_var("sp_fiq"^i,``:word32``)	   ,
	     mk_var("sp_irq"^i,``:word32``), mk_var("sp_svc"^i,``:word32``)	   ,
	     mk_var("sp_abt"^i,``:word32``), mk_var("sp_und"^i,``:word32``)	   ,
	     mk_var("sp_mon"^i,``:word32``), mk_var("lr"^i,``:word32``)	           ,
	     mk_var("lr_fiq"^i,``:word32``), mk_var("lr_irq"^i,``:word32``)	   ,
	     mk_var("lr_svc"^i,``:word32``), mk_var("lr_abt"^i,``:word32``)	   ,
	     mk_var("lr_und"^i,``:word32``), mk_var("lr_mon"^i,``:word32``)	   ,
	     mk_var("pc"^i,``:word32``)] in
	listSyntax.mk_list (reg_names , ``:word32``)
     
    end;
	      

val mk_regs_def = 
    Define ` mk_regs rv = 
				RName_case  (EL 0 rv)
					    (EL 1 rv)
					    (EL 2 rv)
					    (EL 3 rv)
					    (EL 4 rv) 
					    (EL 5 rv) 
					    (EL 6 rv) 
					    (EL 7 rv) 
					    (EL 8 rv) 
					    (EL 9 rv) 
					    (EL 10 rv) 
					    (EL 11 rv)  
					    (EL 12 rv)  
					    (EL 13 rv)  
					    (EL 14 rv)  
					    (EL 15 rv)  
					    (EL 16 rv)  
					    (EL 17 rv)  
					    (EL 18 rv)  
					    (EL 19 rv)  
					    (EL 20 rv)  
					    (EL 21 rv)  
					    (EL 22 rv)  
					    (EL 23 rv)  
					    (EL 24 rv)  
					    (EL 25 rv)  
					    (EL 26 rv)  
					    (EL 27 rv)  
					    (EL 28 rv)  
					    (EL 29 rv)  
					    (EL 30 rv)  
					    (EL 31 rv)  
					    (EL 32 rv)`; 



fun build_sym_state_loc i =
    let 
	val reg_list = gen_reg_names i 
	val user_reg_list = gen_user_reg_names i 
	val mem = mk_var("mem"^i,``:bool[32] -> bool[8]``)
	val loc_psr_builder =
	 fn mode =>
            let val loc_name = "_"^mode ^ "_" ^ i
		val (psr_list , it1, ge,res, m) = 
		    (gen_psr_names loc_name, mk_var("it"^loc_name,``:bool[8]``),
		     mk_var("ge"^loc_name,``:bool[4]``),
		     mk_var("res"^loc_name,``:bool[4]``),
		     mk_var("m"^loc_name,``:bool[5]``)) 
	    in
		``(mk_psrs ^psr_list ^it1 ^ge ^res ^m)``
	    end
	val cpsr = loc_psr_builder "curr"
	val fiq = loc_psr_builder "fiq"
	val irq = loc_psr_builder "irq"
	val svc = loc_psr_builder "svc"
	val mon = loc_psr_builder "mon"
	val abt = loc_psr_builder "abt"
	val und = loc_psr_builder "und"
	val state =
	    ``<| registers := proc 0  (mk_regs ^reg_list);
                 psrs := proc 0  (PSRName_case
			 ^cpsr ^fiq ^irq ^svc ^mon ^abt ^und
		    );
	         coprocessors := <| state :=  <|
                   cp15 := <|
                     SCTLR := <|
				  EE:= ^(mk_var ("cop_ee"^i, ``:bool``)) ;
	                          V:= ^(mk_var ("cop_v"^i, ``:bool``))
                     |>;
		     C1 := ^(mk_var ("cop_c1"^i, ``:bool[32]``));
		     C2 := ^(mk_var ("cop_c2"^i, ``:bool[32]``));
		     C3 := ^(mk_var ("cop_c3"^i, ``:bool[32]``))
                   |>
                 |> |>;
                  memory :=  ^mem |> ``;
	val state = EVAL state;
	val (_, post) = dest_thm state;
	val (_, state) = dest_eq post;
    in
	state
    end;



fun my_eval exp =
    let val th = EVAL exp
	val (_, post) = dest_thm th
	val (_, res) = dest_eq post
    in res
    end;



val RName_User_case_axiom = new_axiom("RName_User_case_axiom", ``
			  ! r0:bool[32] r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 sp lr pc
                     r0' r1' r2' r3' r4' r5' r6' r7' r8' r9' r10' r11' r12' sp' lr' pc'.
      (RName_User_case r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 sp lr pc =
       RName_User_case r0' r1' r2' r3' r4' r5' r6' r7' r8' r9' r10' r11' r12' sp' lr' pc')       =
       ((r0 = r0') /\  (r1=r1') /\  (r2 = r2') /\ (r3 = r3') /\  (r4=r4') /\
             (r5=r5') /\ (r6=r6') /\ (r7=r7') /\ (r8=r8') /\ (r9=r9') /\ (r10=r10') /\
            (r11=r11') /\ (r12 = r12') /\ (sp = sp') /\ (lr = lr') /\
									(pc = pc'))``);

val guests_diff_axiom = new_axiom("guests_diff_axiom", ``
			  global_vm_0_add <> global_vm_1_add``);


fun gen_hol_invariant state =
    let val invariant_eval = SIMP_RULE (srw_ss()) [] (ASSUME ``(kth_hyp_invariants ^state)``)
	val invariant = (computeLib.RESTR_EVAL_RULE [``read_mem32`` ] (invariant_eval))
	val invariant_con = concl invariant
    in
	invariant_con
    end;
			    


(*post-condition send*) 
fun send_gen_hol_postcondition () =
    let 
	val rsb = build_sym_state_loc  "_rl2"
	val is1_m1 = build_sym_state_loc  "_ila"
	val is1_m2 = build_sym_state_loc  "_ilb"
	val log_comp1 = mk_log_comp "1" ``guest1``
	val is1 = my_eval ``mk_comp_arm_state ^is1_m1 ^log_comp1 ^is1_m2``

	val is2_based_on_is1 = my_eval ``case send_message_ideal  ^is1 ^is1 ic (<| proc:=0 |>) of 
				     (ValueState b1 is2, ic2 ,mode) ->
				     is2``
	val rs2_based_on_is2 = ASSUME ``
		let g = guest1 in ! rs2 is2. (correct_user_mode_states rs2 is2 g)``
	val post_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``]
						   rs2_based_on_is2
	val post_eval = SPECL [rsb , is2_based_on_is1, ``(<| proc:=0 |>)``] post_eval
	val post_eval = SIMP_RULE (srw_ss()) [RName_User_case_axiom] post_eval
	val post = (computeLib.RESTR_EVAL_RULE [``read_mem32``] (post_eval))
	val post_con = concl post

	val invariant_con = gen_hol_invariant rsb
    in
	(* ``^post_con /\ ^invariant_con`` *)
	(rsb, post_con)
    end;

(*post-condition send*) 
fun send_gen_hol_precondition () =
    let 
(* Where is written that I'm doing SI 1 *)
	val is1_m1 = build_sym_state_loc  "_ila"
	val is1_m2 = build_sym_state_loc  "_ilb"
	val log_comp1 = mk_log_comp "1" ``guest1``
	val is1 = my_eval ``mk_comp_arm_state ^is1_m1 ^log_comp1 ^is1_m2``
	val rsa = build_sym_state_loc  "_rl1"
	val rs1_based_on_is1 = ASSUME ``! rs1. 
   let  m_ila = 19w in
(ARM_MODE rs1=19w) ==> 
(correct_switched_mode_states rs1 ^is1 guest1
)``
	val pre_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``] rs1_based_on_is1 
	val pre_eval = SPECL [rsa, ``(<| proc:=0 |>):iiid`` ] pre_eval
	val term_pre = concl pre_eval
	val pre_eval = ASSUME ``^term_pre /\ 
					       (
        let active_machine = get_active_machine ^is1 in
   let pc = (case read_pc (<| proc:=0 |>) active_machine  of
         			  ValueState t  s -> t)    in
       let instr = read_mem32 pc active_machine.memory in
	   (instr = 0xEF000001w)
  )
				  ``
	val pre_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``] pre_eval
	val pre_eval = SIMP_RULE (srw_ss()) [RName_User_case_axiom] pre_eval
	val pre = (computeLib.RESTR_EVAL_RULE [``read_mem32`` ] (pre_eval))
	val pre_con = concl pre

	val invariant_con = gen_hol_invariant rsa
    in
	(* ``^pre_con /\ ^invariant_con`` *)
	(rsa, pre_con)
    end;


fun release_gen_hol_postcondition () =
    let 
	val rsb = build_sym_state_loc  "_rl2"
	val is1_m1 = build_sym_state_loc  "_ila"
	val is1_m2 = build_sym_state_loc  "_ilb"
	val log_comp1 = mk_log_comp "1" ``guest1``
	val is1 = my_eval ``mk_comp_arm_state ^is1_m1 ^log_comp1 ^is1_m2``

	val is2_based_on_is1 = my_eval ``case release_ideal  ^is1 ^is1 ic (<| proc:=0 |>) of 
				     (ValueState b1 is2, ic2 ,mode) ->
				     is2``
	val rs2_based_on_is2 = ASSUME ``
		let g = guest1 in ! rs2 is2. (correct_user_mode_states rs2 is2 g)``
	val post_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``]
						   rs2_based_on_is2
	val post_eval = SPECL [rsb , is2_based_on_is1, ``(<| proc:=0 |>)``] post_eval
	val post_eval = SIMP_RULE (srw_ss()) [RName_User_case_axiom] post_eval
	val post = (computeLib.RESTR_EVAL_RULE [``read_mem32``] (post_eval))
	val post_con = concl post

	val invariant_con = gen_hol_invariant rsb
    in
	(* ``^post_con /\ ^invariant_con`` *)
	(rsb, post_con)
    end;


(*post-condition send*) 
fun release_gen_hol_precondition () =
    let 
(* Where is written that I'm doing SI 1 *)
	val is1_m1 = build_sym_state_loc  "_ila"
	val is1_m2 = build_sym_state_loc  "_ilb"
	val log_comp1 = mk_log_comp "1" ``guest1``
	val is1 = my_eval ``mk_comp_arm_state ^is1_m1 ^log_comp1 ^is1_m2``
	val rsa = build_sym_state_loc  "_rl1"
	val rs1_based_on_is1 = ASSUME ``! rs1
									. (correct_switched_mode_states rs1 ^is1 guest1
)``
	val pre_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``] rs1_based_on_is1 
	val pre_eval = SPECL [rsa, ``(<| proc:=0 |>):iiid`` ] pre_eval
	val term_pre = concl pre_eval
	val pre_eval = ASSUME ``^term_pre /\ 
  (
   let active_machine = get_active_machine ^is1 in
   let pc = (case read_pc (<| proc:=0 |>) active_machine  of
         			  ValueState t  s -> t)    in
       let instr = read_mem32 pc active_machine.memory in
	   (instr = 0xEF000000w)
  )
				  ``
	val pre_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``] pre_eval
	val pre_eval = SIMP_RULE (srw_ss()) [RName_User_case_axiom] pre_eval
	val pre = (computeLib.RESTR_EVAL_RULE [``read_mem32`` ] (pre_eval))
	val pre_con = concl pre

	val invariant_con = gen_hol_invariant rsa
    in
	(* ``^pre_con /\ ^invariant_con`` *)
	(rsa, pre_con)
    end;

(* SI error *)
fun si_error_gen_hol_postcondition () =
    let 
	val rsb = build_sym_state_loc  "_rl2"
	val is1_m1 = build_sym_state_loc  "_ila"
	val is1_m2 = build_sym_state_loc  "_ilb"
	val log_comp1 = mk_log_comp "1" ``guest1``
	val is1 = my_eval ``mk_comp_arm_state ^is1_m1 ^log_comp1 ^is1_m2``

	val is2_based_on_is1 = my_eval ``case undefined_SWI_handler_ideal ^is1 ic (<| proc:=0 |>) of 
				     (ValueState b1 is2, ic2 ,mode) ->
				     is2``
	val rs2_based_on_is2 = ASSUME ``
		let g = guest1 in ! rs2 is2. (correct_user_mode_states rs2 is2 g)``
	val post_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``]
						   rs2_based_on_is2
	val post_eval = SPECL [rsb , is2_based_on_is1, ``(<| proc:=0 |>)``] post_eval
	val post_eval = SIMP_RULE (srw_ss()) [RName_User_case_axiom] post_eval
	val post = (computeLib.RESTR_EVAL_RULE [``read_mem32``] (post_eval))
	val post_con = concl post

	val invariant_con = gen_hol_invariant rsb
    in
	(* ``^post_con /\ ^invariant_con`` *)
	(rsb, post_con)
    end;


fun si_error_gen_hol_precondition () =
    let 
(* Where is written that I'm doing SI 1 *)
	val is1_m1 = build_sym_state_loc  "_ila"
	val is1_m2 = build_sym_state_loc  "_ilb"
	val log_comp1 = mk_log_comp "1" ``guest1``
	val is1 = my_eval ``mk_comp_arm_state ^is1_m1 ^log_comp1 ^is1_m2``
	val rsa = build_sym_state_loc  "_rl1"
	val rs1_based_on_is1 = ASSUME ``! rs1
									. (correct_switched_mode_states rs1 ^is1 guest1
)``
	val pre_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``] rs1_based_on_is1 
	val pre_eval = SPECL [rsa, ``(<| proc:=0 |>):iiid`` ] pre_eval
	val term_pre = concl pre_eval
	val pre_eval = ASSUME ``^term_pre /\ 
  (
   let active_machine = get_active_machine ^is1 in
   let pc = (case read_pc (<| proc:=0 |>) active_machine  of
         			  ValueState t  s -> t)    in
       let instr = read_mem32 pc active_machine.memory in
	   (instr <> 0xEF000000w) /\ (instr <> 0xEF000001w)
  )
				  ``
	val pre_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``] pre_eval
	val pre_eval = SIMP_RULE (srw_ss()) [RName_User_case_axiom] pre_eval
	val pre = (computeLib.RESTR_EVAL_RULE [``read_mem32`` ] (pre_eval))
	val pre_con = concl pre

	val invariant_con = gen_hol_invariant rsa
    in
	(* ``^pre_con /\ ^invariant_con`` *)
	(rsa, pre_con)
    end;


(* prefetch error *)
fun prefetch_gen_hol_postcondition () =
    let 
	val rsb = build_sym_state_loc  "_rl2"
	val is1_m1 = build_sym_state_loc  "_ila"
	val is1_m2 = build_sym_state_loc  "_ilb"
	val log_comp1 = mk_log_comp "1" ``guest1``
	val is1 = my_eval ``mk_comp_arm_state ^is1_m1 ^log_comp1 ^is1_m2``

	val is2_based_on_is1 = my_eval ``case prefetch_abort_handler_ideal ^is1 ic (<| proc:=0 |>) of 
				     (ValueState b1 is2, ic2 ,mode) ->
				     is2``
	val rs2_based_on_is2 = ASSUME ``
		let g = guest1 in ! rs2 is2. (correct_user_mode_states rs2 is2 g)``
	val post_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``]
						   rs2_based_on_is2
	val post_eval = SPECL [rsb , is2_based_on_is1, ``(<| proc:=0 |>)``] post_eval
	val post_eval = SIMP_RULE (srw_ss()) [RName_User_case_axiom] post_eval
	val post = (computeLib.RESTR_EVAL_RULE [``read_mem32``] (post_eval))
	val post_con = concl post

	val invariant_con = gen_hol_invariant rsb
    in
	(* ``^post_con /\ ^invariant_con`` *)
	(rsb, post_con)
    end;


fun prefetch_gen_hol_precondition () =
    let 
(* Where is written that I'm doing SI 1 *)
	val is1_m1 = build_sym_state_loc  "_ila"
	val is1_m2 = build_sym_state_loc  "_ilb"
	val log_comp1 = mk_log_comp "1" ``guest1``
	val is1 = my_eval ``mk_comp_arm_state ^is1_m1 ^log_comp1 ^is1_m2``
	val rsa = build_sym_state_loc  "_rl1"
	val rs1_based_on_is1 = ASSUME ``! rs1
									. (correct_switched_mode_states rs1 ^is1 guest1
)``
	val pre_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``] rs1_based_on_is1 
	val pre_eval = SPECL [rsa, ``(<| proc:=0 |>):iiid`` ] pre_eval
	val pre_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``] pre_eval
	val pre_eval = SIMP_RULE (srw_ss()) [RName_User_case_axiom] pre_eval
	val pre = (computeLib.RESTR_EVAL_RULE [``read_mem32`` ] (pre_eval))
	val pre_con = concl pre

	val invariant_con = gen_hol_invariant rsa
    in
	(* ``^pre_con /\ ^invariant_con`` *)
	(rsa, pre_con)
    end;

(* data error *)
fun data_gen_hol_postcondition () =
    let 
	val rsb = build_sym_state_loc  "_rl2"
	val is1_m1 = build_sym_state_loc  "_ila"
	val is1_m2 = build_sym_state_loc  "_ilb"
	val log_comp1 = mk_log_comp "1" ``guest1``
	val is1 = my_eval ``mk_comp_arm_state ^is1_m1 ^log_comp1 ^is1_m2``

	val is2_based_on_is1 = my_eval ``case data_abort_handler_ideal ^is1 ic (<| proc:=0 |>) of 
				     (ValueState b1 is2, ic2 ,mode) ->
				     is2``
	val rs2_based_on_is2 = ASSUME ``
		let g = guest1 in ! rs2 is2. (correct_user_mode_states rs2 is2 g)``
	val post_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``]
						   rs2_based_on_is2
	val post_eval = SPECL [rsb , is2_based_on_is1, ``(<| proc:=0 |>)``] post_eval
	val post_eval = SIMP_RULE (srw_ss()) [RName_User_case_axiom] post_eval
	val post = (computeLib.RESTR_EVAL_RULE [``read_mem32``] (post_eval))
	val post_con = concl post

	val invariant_con = gen_hol_invariant rsb
    in
	(* ``^post_con /\ ^invariant_con`` *)
	(rsb, post_con)
    end;


fun data_gen_hol_precondition () = prefetch_gen_hol_precondition ();

(* undefined *)
fun undefined_gen_hol_postcondition () =
    let 
	val rsb = build_sym_state_loc  "_rl2"
	val is1_m1 = build_sym_state_loc  "_ila"
	val is1_m2 = build_sym_state_loc  "_ilb"
	val log_comp1 = mk_log_comp "1" ``guest1``
	val is1 = my_eval ``mk_comp_arm_state ^is1_m1 ^log_comp1 ^is1_m2``

	val is2_based_on_is1 = my_eval ``case undefined_instr_handler_ideal ^is1 ic (<| proc:=0 |>) of 
				     (ValueState b1 is2, ic2 ,mode) ->
				     is2``
	val rs2_based_on_is2 = ASSUME ``
		let g = guest1 in ! rs2 is2. (correct_user_mode_states rs2 is2 g)``
	val post_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``]
						   rs2_based_on_is2
	val post_eval = SPECL [rsb , is2_based_on_is1, ``(<| proc:=0 |>)``] post_eval
	val post_eval = SIMP_RULE (srw_ss()) [RName_User_case_axiom] post_eval
	val post = (computeLib.RESTR_EVAL_RULE [``read_mem32``] (post_eval))
	val post_con = concl post

	val invariant_con = gen_hol_invariant rsb
    in
	(* ``^post_con /\ ^invariant_con`` *)
	(rsb, post_con)
    end;


fun undefined_gen_hol_precondition () = prefetch_gen_hol_precondition ();

(*post-condition send*) 
fun schedule_gen_hol_postcondition () =
    let 
	val rsb = build_sym_state_loc  "_rl2"
	val is1_m1 = build_sym_state_loc  "_ila"
	val is1_m2 = build_sym_state_loc  "_ilb"
	val log_comp1 = mk_log_comp "1" ``guest1``
	val is1 = my_eval ``mk_comp_arm_state ^is1_m1 ^log_comp1 ^is1_m2``

	val is2_based_on_is1 = my_eval ``case simple_schedule_ideal  ^is1  ic (<| proc:=0 |>) of 
				     (ValueState b1 is2, ic2 ,mode) ->
				     is2``
	val rs2_based_on_is2 = ASSUME ``
		let g = guest2 in ! rs2 is2. (correct_user_mode_states rs2 is2 g)``
	val post_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``]
						   rs2_based_on_is2
	val post_eval = SPECL [rsb , is2_based_on_is1, ``(<| proc:=0 |>)``] post_eval
	val post_eval = SIMP_RULE (srw_ss()) [RName_User_case_axiom] post_eval
	val post = (computeLib.RESTR_EVAL_RULE [``read_mem32``] (post_eval))
	val post_con = concl post

	val invariant_con = gen_hol_invariant rsb
    in
	(* ``^post_con /\ ^invariant_con`` *)
	(rsb, post_con)
    end;

fun schedule_gen_hol_precondition () =
    let 
(* Where is written that I'm doing SI 1 *)
	val is1_m1 = build_sym_state_loc  "_ila"
	val is1_m2 = build_sym_state_loc  "_ilb"
	val log_comp1 = mk_log_comp "1" ``guest1``
	val is1 = my_eval ``mk_comp_arm_state ^is1_m1 ^log_comp1 ^is1_m2``
	val rsa = build_sym_state_loc  "_rl1"
	val rs1_based_on_is1 = ASSUME ``! rs1
									. (correct_switched_mode_states rs1 ^is1 guest1
)``
	val pre_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``] rs1_based_on_is1 
	val pre_eval = SPECL [rsa, ``(<| proc:=0 |>):iiid`` ] pre_eval
	val term_pre = concl pre_eval
	val pre_eval = ASSUME ``^term_pre /\ 
  (
  let state = ^is1 in
  let active_machine_id = state.logical_component.active_machine in
  let (is_ready, any_message, next_active_id, message, msg_handler_adr) = 
    if( active_machine_id = guest1) then
	(state.logical_component.ready2 , state.logical_component.box_full2, guest2, 
	 state.logical_component.message_box2, ideal_addresses.guest2_msg_handler_adr)
    else
	(state.logical_component.ready1 , state.logical_component.box_full1, guest1, 
	 state.logical_component.message_box1 , ideal_addresses.guest1_msg_handler_adr) in
   (~is_ready \/ ~any_message)
  )
				  ``
	val pre_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``] pre_eval
	val pre_eval = SIMP_RULE (srw_ss()) [RName_User_case_axiom] pre_eval
	val pre = (computeLib.RESTR_EVAL_RULE [``read_mem32`` ] (pre_eval))
	val pre_con = concl pre

	val invariant_con = gen_hol_invariant rsa
    in
	(* ``^pre_con /\ ^invariant_con`` *)
	(rsa, pre_con)
    end;


(*post-condition send*) 
fun receive_gen_hol_postcondition () =
    let 
	val rsb = build_sym_state_loc  "_rl2"
	val is1_m1 = build_sym_state_loc  "_ila"
	val is1_m2 = build_sym_state_loc  "_ilb"
	val log_comp1 = mk_log_comp "1" ``guest1``
	val is1 = my_eval ``mk_comp_arm_state ^is1_m1 ^log_comp1 ^is1_m2``

	val is2_based_on_is1 = my_eval ``
				  case receive_schedule_ideal  ^is1  ic (<| proc:=0 |>) of 
				     (ValueState b1 is2, ic2 ,mode) ->
				     is2``
	val is2_based_on_is1_simp_eq = concl (SIMP_RULE (srw_ss())
				  [guests_diff_axiom] (ASSUME
				  ``aa=^is2_based_on_is1``))
	val (_, is2_based_on_is1) = dest_eq is2_based_on_is1_simp_eq

	val rs2_based_on_is2 = ASSUME ``
		let g = guest2 in ! rs2 is2. (correct_user_mode_states rs2 is2 g)``
	val post_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``]
						   rs2_based_on_is2
	val post_eval = SPECL [rsb , is2_based_on_is1, ``(<| proc:=0 |>)``] post_eval
	val post_eval = SIMP_RULE (srw_ss()) [RName_User_case_axiom] post_eval
	val post = (computeLib.RESTR_EVAL_RULE [``read_mem32``] (post_eval))
	val post_con = concl post

	val invariant_con = gen_hol_invariant rsb
    in
	(* ``^post_con /\ ^invariant_con`` *)
	(rsb, post_con)
    end;

fun receive_gen_hol_precondition () =
    let 
(* Where is written that I'm doing SI 1 *)
	val is1_m1 = build_sym_state_loc  "_ila"
	val is1_m2 = build_sym_state_loc  "_ilb"
	val log_comp1 = mk_log_comp "1" ``guest1``
	val is1 = my_eval ``mk_comp_arm_state ^is1_m1 ^log_comp1 ^is1_m2``
	val rsa = build_sym_state_loc  "_rl1"
	val rs1_based_on_is1 = ASSUME ``! rs1
									. (correct_switched_mode_states rs1 ^is1 guest1
)``
	val pre_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``] rs1_based_on_is1 
	val pre_eval = SPECL [rsa, ``(<| proc:=0 |>):iiid`` ] pre_eval
	val term_pre = concl pre_eval
	val pre_eval = ASSUME ``^term_pre /\ 
  (
  let state = ^is1 in
  let active_machine_id = state.logical_component.active_machine in
  let (is_ready, any_message, next_active_id, message, msg_handler_adr) = 
    if( active_machine_id = guest1) then
	(state.logical_component.ready2 , state.logical_component.box_full2, guest2, 
	 state.logical_component.message_box2, ideal_addresses.guest2_msg_handler_adr)
    else
	(state.logical_component.ready1 , state.logical_component.box_full1, guest1, 
	 state.logical_component.message_box1 , ideal_addresses.guest1_msg_handler_adr) in
   ~(~is_ready \/ ~any_message)
  )
				  ``
	val pre_eval = computeLib.RESTR_EVAL_RULE [``read_mem32``] pre_eval
	val pre_eval = SIMP_RULE (srw_ss()) [RName_User_case_axiom] pre_eval
	val pre = (computeLib.RESTR_EVAL_RULE [``read_mem32`` ] (pre_eval))
	val pre_con = concl pre

	val invariant_con = gen_hol_invariant rsa
    in
	(* ``^pre_con /\ ^invariant_con`` *)
	(rsa, pre_con)
    end;


fun remove_access_violation thm =
    LIST_CONJ (List.filter (fn thm2 =>
			       not ((can (ho_match_term [] empty_tmset
						  ``~access_violation
				   x``))
				  (concl thm2))
			)  (CONJUNCTS thm));

fun is_real_mem_eq_ideal_mem thm = 
    (can (ho_match_term [] empty_tmset
		    ``!a. (p1 ==>  (mem_rl1 a = mem_ila a)) /\
                          (p2 ==>  (mem_rl1 a = mem_ila a))``)) (concl
    thm);
fun is_real_mem_eq_ideal_mem_term term = 
    (can (ho_match_term [] empty_tmset
		    ``!a. (p1 ==>  (mem_rl1 a = mem_ila a)) /\
                          (p2 ==>  (mem_rl1 a = mem_ila a))``)) term;

fun extract_from_goals goals p =
    List.nth (
    List.filter (
    fn (h,predicate) =>
       p predicate
    ) goals
    , 0);

fun discharge_from_goals goals goal =
    List.filter (
    fn goal1 =>
       (not (goal1 = goal))
    ) goals;

fun match_with_constants constants pat thm =
    let  val (tm_inst, ty_inst) =
             ho_match_term [] empty_tmset pat (concl thm)
	 val bound_vars = map #redex tm_inst
    in
	null (intersect constants bound_vars)
    end handle HOL_ERR _ => false;

fun match_with_constants_term constants pat tm =
    let  val (tm_inst, ty_inst) =
             ho_match_term [] empty_tmset pat tm
	 val bound_vars = map #redex tm_inst
    in
	null (intersect constants bound_vars)
    end handle HOL_ERR _ => false;

fun is_executed_si_ideal_mem thm = 
    ((match_with_constants [``lr_svc_ila:bool[32]``, ``mem_ila``] ``read_mem32 ((lr_svc_ila:bool[32])+v1)
    mem_ila = v2`` thm)
     orelse
     (match_with_constants [``lr_svc_ila:bool[32]``, ``mem_ila``] ``read_mem32 ((lr_svc_ila:bool[32])+v1)
    mem_ila <> v2`` thm)
    );



fun discard_real_mem_eq_ideal_mem thms =
    (List.filter (fn thm => (not (is_real_mem_eq_ideal_mem thm))) thms);

fun extract_real_mem_eq_ideal_mem thms =
    (List.hd (List.filter is_real_mem_eq_ideal_mem  thms));

fun extract_executed_si_ideal_mem thms =
    (LIST_CONJ (List.filter is_executed_si_ideal_mem  thms));


fun extract_lr_svc_ideal_max thms =
    (List.hd 
    (List.filter (match_with_constants [``lr_svc_ila:bool[32]``]
				       ``lr_svc_ila ≤₊ a``)
		 thms));
fun extract_lr_svc_ideal_min thms =
    (List.hd 
    (List.filter (match_with_constants [``lr_svc_ila:bool[32]``]
				       ``lr_svc_ila ≥₊ a``)
		 thms));
fun extract_lr_svc_real_max thms =
    (List.hd 
    (List.filter (match_with_constants [``lr_svc_rl1:bool[32]``]
				       ``lr_svc_rl1 ≤₊ a``)
		 thms));
fun extract_lr_svc_real_min thms =
    (List.hd 
    (List.filter (match_with_constants [``lr_svc_rl1:bool[32]``]
				       ``lr_svc_rl1 ≥₊ a``)
		 thms));



fun extract_lr_svc_real_range thms =
    (List.hd 
    (List.filter (match_with_constants [``I_curr__rl1:bool``]
				       ``I_curr__rl1 /\ p1``)
		 thms));

fun extract_id_mode thms =
    (List.hd 
    (List.filter (match_with_constants [``m_curr__ila:bool[5]``]
				       ``m_curr__ila:bool[5] = v``)
		 thms));

fun extract_lr_svc_real_eq_ideal thms =
    (List.hd 
    (List.filter (match_with_constants [``lr_svc_rl1:bool[32]``]
				       ``lr_svc_rl1:bool[32] = v``)
		 thms));

fun find_all_user_mode_theorems thms =
    let val thms1 = (List.filter (fn thm =>
				     not (null (intersect 
						    [``r0:arm_state``,
						     ``i0:composite_arm_state``]
						    (free_vars (concl thm))
				 )))
				 thms)
    in
	thms1
    end;

fun find_user_mode_theorems thms =
    let val thms1 = find_all_user_mode_theorems thms
	val thms2 = (List.filter
		     (fn thm => not (is_eq (concl thm)))
		     thms1)
    in
	thms2
    end;

fun find_to_rm_user_mode_theorems thms =
    let val thms1 = find_all_user_mode_theorems thms
	val thms2 = (List.filter
		     (fn thm => is_eq (concl thm))
		     thms1)
	val thms3 = (List.filter
		     (fn thm => 
			 let val trm = concl thm
			     val (a,b) = dest_eq trm
			 in
			     not (null (intersect 
					    [``r0:arm_state``,
					     ``i0:composite_arm_state``]
					    (free_vars a)
				 ))
			 end
		     )
		     thms2)
    in
	thms3
    end;

fun standard_simplification thm0 =
    let val thm1 = computeLib.RESTR_EVAL_RULE [``read_mem32``] thm0
	val thm2 = remove_access_violation thm1
	val thm3 = SIMP_RULE (srw_ss()) (RName_User_case_axiom :: hypervisor_guest_mem_axioms) thm2
	val thm4 = computeLib.RESTR_EVAL_RULE [``read_mem32``] thm3
    in
	thm4
    end;

fun standard_simp_tac goal =
    ((computeLib.RESTR_EVAL_TAC [``read_mem32``, ``guests_equal_memory``] THEN 
    SIMP_TAC (srw_ss()) 
    ((RName_User_case_axiom:: hypervisor_guest_mem_axioms)@
     hypervisor_constants_axioms)
    THEN
    computeLib.RESTR_EVAL_TAC [``read_mem32``, ``guests_equal_memory``]) goal);

fun standard_conjunction thm0 =
    LIST_CONJ (List.map (
	       fn thm2 =>
		  standard_simplification thm2
	       )  (CONJUNCTS thm0));

fun extract_thm_specific_precondition_conj thm0 =
    List.map (
	       fn thm2 =>
		  standard_simplification thm2
	       )  (List.tl (List.tl (CONJUNCTS thm0)));

(* Experiments for the new generation of pre/post condition *)
fun new_gen_precondition mode_value other_condition =
    (* build the sym stated *)
    let val is1_m1 = build_sym_state_loc "_ila"
	val is1_m2 = build_sym_state_loc "_ilb"
	val log_comp1 = mk_log_comp "1" ``guest1``
	val is1 = my_eval ``mk_comp_arm_state ^is1_m1 ^log_comp1 ^is1_m2``
	val rsa = build_sym_state_loc "_rl1"

	(* Assume the theorem and the additional precondition *)
	val thm = ASSUME ``
	((outer_full_relation_switch ^rsa ^is1 r0 i0 guest1) /\
         (outer_full_relation_user r0 i0 guest1)
	)  /\
	((^is1.machine1.psrs(0, CPSR)).M = ^mode_value) /\
        ^other_condition ^is1
	``

	(* Extract the theorem on mode and executed SI *)
	val [thm_ideal_mode, thm_other_prop] =
	    extract_thm_specific_precondition_conj thm

	(* Compute the mode of the real world *)
	val thm1 = SIMP_RULE (simpLib.mk_simpset [boolSimps.LET_ss])
			     [correct_switched_mode_states_def,
			     outer_full_relation_switch_def]
			     thm
	val thm_eq_mode = List.nth ((CONJUNCTS thm1), 0)
	val thm_eq_mode1 = EVAL_RULE thm_eq_mode
	val thm_eq_mode2 = List.nth ((CONJUNCTS thm_eq_mode1), 0)
	val thm_real_mode = SIMP_RULE (srw_ss())  [thm_ideal_mode] thm_eq_mode2

	(* Apply the real and ideal mode mode *)
	val thm2 = SIMP_RULE (srw_ss())  [] thm1
	val thm3 = SIMP_RULE (srw_ss())  [thm_ideal_mode, thm_real_mode] thm2

	val prevent = [``mmu_boot_setup``,
		       ``guests_equal_memory``,
		      ``read_mem32``]
	val thm4 = computeLib.RESTR_EVAL_RULE prevent thm3
	val thm5 = SIMP_RULE (srw_ss())  
			     (RName_User_case_axiom
			      ::hypervisor_constants_axioms)
			     thm4
	val thm6 = computeLib.RESTR_EVAL_RULE prevent thm5
	val user_correct_thms = find_user_mode_theorems (CONJUNCTS thm6)
	val thm7 = REWRITE_RULE user_correct_thms  thm6
	val user_correct_thms_to_remove = find_to_rm_user_mode_theorems (CONJUNCTS thm7)
	val thm8 = REWRITE_RULE user_correct_thms_to_remove  thm7
	val user_correct_thms_to_remove2 =
		       find_to_rm_user_mode_theorems (CONJUNCTS thm8)
	val thm9 = REWRITE_RULE user_correct_thms_to_remove2  thm8
    in
	(thm9, thm_ideal_mode, thm_other_prop, rsa, thm)
    end;

fun si_generate_full_precondition mode_value other_condition other_gen_condition=
    let val (thm_simp, thm_ideal_mode, thm_other_prop, rsa, thm) =
	    new_gen_precondition mode_value other_condition
	val thm_simp_exp_eq_mem = SIMP_RULE (srw_ss())
					    (guests_equal_memory_def::
					     hypervisor_guest_mem_axioms)
					     thm_simp
	val thms = CONJUNCTS thm_simp_exp_eq_mem
	val mem_eq_thm = extract_real_mem_eq_ideal_mem thms
	val si_id_thm = extract_executed_si_ideal_mem thms
	val lr_svc_id_min_thm = extract_lr_svc_ideal_min thms
	val lr_svc_id_max_thm = extract_lr_svc_ideal_max thms
	val lr_svc_rl_min_thm = extract_lr_svc_real_min thms
	val lr_svc_rl_max_thm = extract_lr_svc_real_max thms

	val lr_svc_rl_eq_id_thm = extract_lr_svc_real_eq_ideal thms
	val impls =
	    List.tabulate(4, (fn x =>
		     let val offset = wordsSyntax.mk_wordii (x+1,32)
			 val spec_thm = EVAL_RULE (SPEC
					``lr_svc_rl1:bool[32]-(^offset)``
					mem_eq_thm)
			 val impl_tm = concl (hd (CONJUNCTS spec_thm))
			 val (hyp_tm, _) = dest_imp impl_tm
		     in
			 hyp_tm
		     end
		 ))
	val thm_hyp = map (
		      fn tm =>
			 blastLib.BBLAST_PROVE (``
			 ^(concl lr_svc_rl_min_thm) ==>
			 ^(concl lr_svc_rl_max_thm) ==>
			 ^(tm)
                      ``)
		      ) impls
	val term_mem_real =  ``(^(concl thm))
	==>
	(^other_gen_condition ^rsa)``
	val th_mem_real = prove (term_mem_real,
               DISCH_TAC THEN
			 EVAL_TAC THEN
			 (SIMP_TAC (srw_ss()) []) THEN
			 EVAL_TAC THEN
			 (* (REWRITE_TAC [minus_one_thm]) THEN *)
			 (ASSUME_TAC lr_svc_rl_min_thm) THEN
			 (ASSUME_TAC lr_svc_rl_max_thm) THEN
			 (MAP_EVERY (fn thm => (ASSUME_TAC (UNDISCH_ALL thm))) thm_hyp)
			 THEN
			 (ASSUME_TAC mem_eq_thm)
			 THEN
			 (MAP_EVERY (fn offset =>
					(ASSUME_TAC 
					     (EVAL_RULE
					     (SPEC
	``lr_svc_rl1:bool[32]-^offset`` mem_eq_thm))))
				    (List.tabulate (4, fn x =>
							 wordsSyntax.mk_wordii (x+1,32))))
			 THEN
			 (ASSUME_TAC (
			  EVAL_RULE (SIMP_RULE (srw_ss()) [] (EVAL_RULE si_id_thm))
			 )) THEN
			 (ASSUME_TAC lr_svc_rl_eq_id_thm) THEN
			 (FULL_SIMP_TAC (srw_ss()) []))
	val end_mem_condition_thm = (UNDISCH th_mem_real)
	val end_mem_condition_thm = (computeLib.RESTR_EVAL_RULE
					 [``read_mem32``]
					 end_mem_condition_thm)
    in
	(thm_simp, thm_ideal_mode, thm_other_prop, end_mem_condition_thm, rsa, thm)
    end;




fun send_generate_full_postcondition thm thm_ideal_mode
    thm_mem_guest guest = 
    let val rsb = build_sym_state_loc "_rl2"
	val is1_m1 = build_sym_state_loc "_ila"
	val is1_m2 = build_sym_state_loc "_ilb"
	val log_comp1 = mk_log_comp "1" ``guest1``
	val is1 = my_eval ``mk_comp_arm_state ^is1_m1 ^log_comp1 ^is1_m2``
	val is2 = ``case transform_state_ideal ^is1 cycle (^is1.machine1.psrs(0,CPSR)).M ((<| proc:=0 |>):iiid) of
               (ValueState b1 is2, ic2 ,mode) -> is2``

	val goal1 =([
	    concl thm
	    ]:term list, ``outer_full_relation_user ^rsb ^is2 ^guest``)
	val prevent2 = [``outer_full_relation_user``,
		       ``read_mem32``,
		       ``send_message_ideal``,
		       ``release_ideal``,
		       ``undefined_SWI_handler_ideal``,
		       ``simple_schedule_ideal``,
		       ``receive_schedule_ideal``,
		       ``prefetch_abort_handler_ideal``,
		       ``data_abort_handler_ideal``,
		       ``undefined_instr_handler_ideal``]

	val (goal2::[], _) = (computeLib.RESTR_EVAL_TAC prevent2) goal1
	val (goal3::[], _) = (SIMP_TAC (srw_ss())  [thm_ideal_mode]) goal2
	val (goal4::[], _) = (computeLib.RESTR_EVAL_TAC prevent2) goal3
	val (goal5::[], _) = (SIMP_TAC (srw_ss())  [thm_mem_guest, DISJ_COMM]) goal4
	val (goal6::[], _) = (computeLib.RESTR_EVAL_TAC
			  [``outer_full_relation_user``,
			  ``read_mem32``])
			  goal5
	val (goal7::[], _) = (SIMP_TAC (bool_ss)
		     [outer_full_relation_user_def]) goal6
	val (correct_user::others, _) = (REPEAT STRIP_TAC) goal7
	val (goal8::[], _) = (SIMP_TAC (simpLib.mk_simpset [boolSimps.LET_ss])
		     [correct_user_mode_states_def]) correct_user
	val (goals10, _) = ((REPEAT STRIP_TAC) THEN standard_simp_tac) goal8
	(* val (goals9, _) = REPEAT STRIP_TAC goal8 *)
	(* val goals10_with_val = map standard_simp_tac goals9 *)
	(* val goals10 = map (fn (g::[],_) => g) goals10_with_val *)
    in
	goals10@others
    end;
