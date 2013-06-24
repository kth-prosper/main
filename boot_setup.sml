infix \\ << >>;

val op \\ = op THEN;

val proc_def = zDefine `proc (n:num) f = \(i,x). if i = n then f x
						 else ARB`;
val proc = Q.store_thm("proc", `proc n f (n,x) = f x`, SRW_TAC []
						 [proc_def]);

val tm1 = ``((n:num,r:RName) =+ d:word32)``

  val tm2 =
    ``proc n
        (RName_case r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
                    r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 r25
                    r26 r27 r28 r29 r30 r31 (r32:word32))``

  fun reg n = mk_var ("r" ^ Int.toString n, ``:word32``)

  fun reg_update (n,name) =
        mk_eq (mk_comb (Term.subst [``r:RName`` |-> name] tm1, tm2),
               Term.subst [reg n  |-> ``d:word32``] tm2)

  val thm = list_mk_conj (map reg_update (Lib.zip (List.tabulate(33,I))
           [``RName_0usr:RName ``, ``RName_1usr:RName ``, ``RName_2usr:RName ``, ``RName_3usr:RName``,
            ``RName_4usr:RName ``, ``RName_5usr:RName ``, ``RName_6usr:RName ``, ``RName_7usr:RName``,
            ``RName_8usr:RName ``, ``RName_8fiq:RName ``, ``RName_9usr:RName ``, ``RName_9fiq:RName``,
            ``RName_10usr:RName``, ``RName_10fiq:RName``, ``RName_11usr:RName``, ``RName_11fiq:RName``,
            ``RName_12usr:RName``, ``RName_12fiq:RName``,
            ``RName_SPusr:RName``, ``RName_SPfiq:RName``, ``RName_SPirq:RName``, ``RName_SPsvc:RName``,
            ``RName_SPabt:RName``, ``RName_SPund:RName``, ``RName_SPmon:RName``,
            ``RName_LRusr:RName``, ``RName_LRfiq:RName``, ``RName_LRirq:RName``, ``RName_LRsvc:RName``,
            ``RName_LRabt:RName``, ``RName_LRund:RName``, ``RName_LRmon:RName``, ``RName_PC:RName``]))

val register_update = Tactical.prove(thm,
    SRW_TAC [] [combinTheory.UPDATE_def, FUN_EQ_THM, proc_def]
      \\ Cases_on `x` \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `r` \\ FULL_SIMP_TAC (srw_ss()) []);

val register_update = save_thm("register_update", GEN_ALL
						      register_update);

local
  val tm1 = ``((n:num,p:PSRName) =+ d:ARMpsr)``
  val tm2 = ``proc n (PSRName_case r0 r1 r2 r3 r4 r5 (r6:ARMpsr))``;

  fun psr n = mk_var ("r" ^ Int.toString n, ``:ARMpsr``)

  fun psr_update (n,name) =
        mk_eq (mk_comb (Term.subst [``p:PSRName`` |-> name] tm1, tm2),
               Term.subst [psr n  |-> ``d:ARMpsr``] tm2)

  val thm = list_mk_conj (map psr_update (Lib.zip (List.tabulate(7,I))
           [``CPSR ``, ``SPSR_fiq ``, ``SPSR_irq ``, ``SPSR_svc``,
            ``SPSR_mon``, ``SPSR_abt``, ``SPSR_und``]))

  val psr_update = Tactical.prove(thm,
    SRW_TAC [] [combinTheory.UPDATE_def, FUN_EQ_THM, proc_def]
      \\ Cases_on `x` \\ SRW_TAC [] [] \\ FULL_SIMP_TAC (srw_ss()) []
      \\ Cases_on `r` \\ FULL_SIMP_TAC (srw_ss()) [])
in
  val psr_update = save_thm("psr_update", GEN_ALL psr_update)
end;


val _ = computeLib.add_persistent_funs
  [("proc", proc), ("register_update", register_update), ("psr_update", psr_update)];






val reset_ideal_machine_def = Define `
reset_ideal_machine init_pc init_mem min_mem max_mem =
let reg_list = GENLIST 
  (\x. if x = 15 then init_pc else 0w:bool[32])
  33 in
let flag_list = MAP
  (\x. F)
  ["N"; "Z"; "C"; "rV"; "Q"; "J"; "E"; "A"; "I"; "F"; "T"] in
let cpsr = mk_psrs flag_list 0w 0w 0w 0b10000w in
let fiq  = mk_psrs flag_list 0w 0w 0w 0b10000w in
let irq  = mk_psrs flag_list 0w 0w 0w 0b10000w in
let svc  = mk_psrs flag_list 0w 0w 0w 0b10000w in
let mon  = mk_psrs flag_list 0w 0w 0w 0b10000w in
let abt  = mk_psrs flag_list 0w 0w 0w 0b10000w in
let und  = mk_psrs flag_list 0w 0w 0w 0b10000w in
let mem = \x:bool[32].
    if x >= min_mem /\ x <= max_mem then
	(init_mem) x
    else
	0w in
<| registers := proc 0  (mk_regs reg_list);
   psrs := proc 0  (PSRName_case
		    cpsr fiq irq svc mon abt und
		   );
    memory :=  mem |>`;

val reset_context_def = Define `
reset_context () = 
let user_regs = GENLIST 
  (\x. 0w:bool[32]) 33 in
let flag_list = MAP
  (\x. F)
  ["N"; "Z"; "C"; "rV"; "Q"; "J"; "E"; "A"; "I"; "F"; "T"] in
let cpsr = mk_psrs flag_list 0w 0w 0w 0b10000w in
<| registers := (mk_user_regs user_regs);
        spsr := cpsr |>
`;


val reset_log_comp_def = Define `
reset_log_comp =
    let context1 = reset_context() in
    let context2 = reset_context() in
    let msg1 = 0w:bool[32] in
    let flg1 = F in
    let rdy1 = T in
    let msg2 = 0w:bool[32] in
    let flg2 = F in
    let rdy2 = T in
 <|
   active_machine  := guest1;
   message_box1    := msg1;
   box_full1       := flg1;
   message_box2    := msg2;
   box_full2       := flg2;
   context1        := context1;
   context2        := context2;
   ready1          := rdy1;
   ready2          := rdy2 
|>
`;

val is = my_eval ``
let init_pc_1 = guest1_min_adr in
let init_mem_1 = G1M:(bool[32]->bool[8]) in
let min_mem_1 = guest1_min_adr in
let max_mem_1 = guest1_max_adr in
let init_pc_2 = guest2_min_adr in
let init_mem_2 = G2M:(bool[32]->bool[8]) in
let min_mem_2 = guest2_min_adr in
let max_mem_2 = guest2_max_adr in
let m1 = reset_ideal_machine init_pc_1 init_mem_1 min_mem_1 max_mem_1 in
let m2 = reset_ideal_machine init_pc_2 init_mem_2 min_mem_2 max_mem_2 in
let cmp = reset_log_comp in
mk_comp_arm_state m1 cmp m2
``;

val rs = build_sym_state_loc "_rl2";

val goal1 = ([]:term list, ``outer_full_relation_user ^rs ^is
							       guest1``);
val prevent2 = [``correct_user_mode_states``,
		``read_mem32``,
		``send_message_ideal``,
		``release_ideal``,
		``undefined_SWI_handler_ideal``,
		``scheduler_ideal``,
		``prefetch_abort_handler_ideal``,
		``data_abort_handler_ideal``,
		``undefined_instr_handler_ideal``];

val (goal2::[], _) = (computeLib.RESTR_EVAL_TAC prevent2) goal1;
val (goal6::[], _) = (computeLib.RESTR_EVAL_TAC
			  [``correct_user_mode_states``,
			  ``read_mem32``])
			  goal2;
val (goal7::[], _) = (SIMP_TAC (simpLib.mk_simpset [boolSimps.LET_ss])
		     [correct_user_mode_states_def]) goal6;
val (goals_conj, _) = (REPEAT STRIP_TAC) goal7;
val goals2 = map standard_simp_tac goals_conj;

List.length goals2;
List.nth (goals2, 0);
List.nth (goals2, 1);
List.nth (goals2, 3);
List.nth (goals2, 4);
List.nth (goals2, 5);
List.nth (goals2, 6);
List.nth (goals2, 7);
List.nth (goals2, 8);
List.nth (goals2, 9);
List.nth (goals2, 10);
List.nth (goals2, 11);
List.nth (goals2, 12);
List.nth (goals2, 13);
List.nth (goals2, 14);
List.nth (goals2, 70);

