use "outer_full_relation.sml";
use "hol-bap.sml";
use "holtoil/handlers_bap_cond_generator.sml";
use "out/hypervisor_values.sml";

fun clear_goal_stack () =
    proofManagerLib.dropn (case proofManagerLib.status()
			    of Manager.PRFS l
			       => List.length l);

fun change_condition_on_imemory cnd =
     let val cnd' = cnd
	 val mbt = ASSUME ``(mem_ila:bool[32]->bool[8]) = (mem_rl1:bool[32]->bool[8])``
	 val cnd_th = REWRITE_RULE [mbt] (ASSUME cnd')
	 val (_, cnd') = dest_thm cnd_th
	 val mbt = ASSUME ``(mem_ilb:bool[32]->bool[8]) = (mem_rl1:bool[32]->bool[8])``
	 val cnd_th = REWRITE_RULE [mbt] (ASSUME cnd')
	 val (_, cnd') = dest_thm cnd_th
     in
	 cnd'
     end;

fun generate_conditions pre_f post_f =
    let val (s2, post) = post_f()
	val (s1, pre) = pre_f()
	(* Remove the quantification from the precondition *)
	val pre' = change_condition_on_imemory pre
	val post' = change_condition_on_imemory post
	(* Add the invariants to the conditions *)
	val inv_pre = gen_hol_invariant(s1)
	val inv_post = gen_hol_invariant(s2)
	val new_pre = ``^pre' /\ ^inv_pre``
	val new_post = ``^post' /\ ^inv_post``
	val new_post = `` ^post'``
	(* Apply all constants obtained by the symbol table *)
	val (_, post_add) = dest_thm (SIMP_RULE (bool_ss) hypervisor_constants_axioms (ASSUME ``^new_post``))
	val (_, pre_add) = dest_thm (SIMP_RULE (bool_ss) hypervisor_constants_axioms (ASSUME ``^new_pre``))
	val (_, pre_end) = dest_thm (computeLib.RESTR_EVAL_RULE [``read_mem32``] (ASSUME pre_add))
	val (_, post_end) = dest_thm (computeLib.RESTR_EVAL_RULE
    [``read_mem32``] (ASSUME post_add))
    in
	(pre_end, post_end)
    end;

fun save_conditions pre_f post_f fname =
    let val (pre, post) = generate_conditions pre_f post_f
	val bap_pre = convert_to_bap_condition(pre)
	val bap_post = convert_to_bap_condition(post)
	val path = "/NOBACKUP/workspaces/robertog/holmodel/verification/out/from_hol/"
	val pre_name = String.concat [path,fname, ".pre.il"]
	val post_name = String.concat [path,fname, ".post.il"]
	val _ = save_bap_condition bap_pre pre_name
	val _ = save_bap_condition bap_post post_name
    in
	1
    end;

save_conditions send_gen_hol_precondition send_gen_hol_postcondition "send";
save_conditions schedule_gen_hol_precondition schedule_gen_hol_postcondition "schedule";
save_conditions receive_gen_hol_precondition
		receive_gen_hol_postcondition "receive";
save_conditions release_gen_hol_precondition release_gen_hol_postcondition "release";

save_conditions si_error_gen_hol_precondition
		si_error_gen_hol_postcondition "si_error";

save_conditions prefetch_gen_hol_precondition
		prefetch_gen_hol_postcondition "prefetch";

save_conditions data_gen_hol_precondition data_gen_hol_postcondition "data";

save_conditions undefined_gen_hol_precondition undefined_gen_hol_postcondition "undefined";


fun save_all handler_name posts =
  let val path =
  "/NOBACKUP/workspaces/robertog/holmodel/verification/out/from_hol2/";
  in
	  map (
	  fn (id, post_bap) =>
	     save_bap_condition post_bap (String.concat
					      [path ,handler_name, ".post.",
					       Int.toString id,
					       ".il"])
	  )
	      (combine (
	       (List.tabulate(List.length posts, fn x => x)) ,
	       (map (fn (h,t) => convert_to_bap_condition t) posts)
	      ))
  end;


fun discard f l =
    List.filter (fn x => not (f x)) l;

fun discard_goal f l =
    List.filter (fn (hyp, c) => not (f c)) l;

fun generate thm thm_ideal_mode thm_mem_guest guest =
    let val hyp = thm
	val goals = send_generate_full_postcondition thm
    thm_ideal_mode thm_mem_guest guest;
	val goals1 = discard_goal (match_with_constants_term [``guests_equal_memory``]
				       ``guests_equal_memory a b``)
			  goals;
	val goals2 = discard_goal (match_with_constants_term [``access_violation``]
	``access_violation a =
	  access_violation b ``) goals1;
	val goals3 = discard_goal (match_with_constants_term [``mmu_boot_setup``]
	``mmu_boot_setup a ``) goals2;
	val goals4_with_val = map standard_simp_tac goals3
	val goals4 = map (fn (g::[],_) => g) goals4_with_val
    in
	goals4
    end;
fun simp_pre thm_simp mem_condition_thm =
    let val pres = (CONJUNCTS thm_simp)@[mem_condition_thm];
	val pres1 = discard (match_with_constants [``guests_equal_memory``]
				       ``guests_equal_memory a b``)
		    pres;
	val pres2 = discard (match_with_constants [``access_violation``]
				       ``¬access_violation a``)
		    pres1;
	val pres3 = discard (match_with_constants [``mmu_boot_setup``]
				       ``mmu_boot_setup a``)
		    pres2;
	val pre_with_inv = SIMP_RULE (srw_ss()) [] (LIST_CONJ pres3);
    in
	pre_with_inv
    end;

val si_other_pre_condition_def = Define `
    si_other_pre_condition  mem_property is =
      let active_machine = get_active_machine is in
      let old_pc = active_machine.registers(0, RName_LRsvc) -4w  in
      let instr = read_mem32 old_pc active_machine.memory in
	  mem_property instr
`;
val si_other_gen_pre_condition_def = Define `
    si_other_gen_pre_condition  mem_property rs =
      let old_pc = rs.registers(0, RName_LRsvc) -4w  in
      let instr = read_mem32 old_pc rs.memory in
	  mem_property instr
`;


val thms_const_to_eval = List.tabulate(
(List.length hypervisor_constants_axioms),
(fn thm_id => 
		  ((concat ["hy_cons_th_", Int.toString thm_id]),
		   List.nth (hypervisor_constants_axioms, thm_id)))
	       
);
val _ = computeLib.add_persistent_funs thms_const_to_eval;




(* SI 1: Precondition *)
val other_condition = ``si_other_pre_condition 
      (\x:bool[32]. (x = 0xEF000001w))``;
val other_gen_condition = ``si_other_gen_pre_condition 
      (\x:bool[32]. (x = 0xEF000001w))``;
val mode_value = ``19w:bool[5]``;
val (thm_simp, thm_ideal_mode, thm_mem_guest, mem_condition_thm,
     rsa, thm)
  = si_generate_full_precondition ``19w:bool[5]`` other_condition other_gen_condition ;
val pre_with_inv = simp_pre thm_simp mem_condition_thm;

val bap_pre = convert_to_bap_condition(concl pre_with_inv);
val path = "/NOBACKUP/workspaces/robertog/holmodel/verification/out/from_hol2/";
val pre_name = String.concat [path,"send", ".pre.il"];
val _ = save_bap_condition bap_pre pre_name;

(* SI 1: Postcondition *)

val guest = ``guest1``;
save_all "send" (generate thm thm_ideal_mode thm_mem_guest guest);


(* RELEASE *)
val other_condition = ``si_other_pre_condition 
      (\x:bool[32]. (x = 0xEF000000w))``;
val other_gen_condition = ``si_other_gen_pre_condition 
      (\x:bool[32]. (x = 0xEF000000w))``;
val (thm_simp, thm_ideal_mode, thm_mem_guest, mem_condition_thm,
     rsa, thm)
  = si_generate_full_precondition ``19w:bool[5]`` other_condition other_gen_condition ;
val pre_with_inv = simp_pre thm_simp mem_condition_thm;

val bap_pre = convert_to_bap_condition(concl pre_with_inv);
val path = "/NOBACKUP/workspaces/robertog/holmodel/verification/out/from_hol2/";
val pre_name = String.concat [path,"release", ".pre.il"];
val _ = save_bap_condition bap_pre pre_name;

val guest = ``guest1``;
save_all "release" (generate thm thm_ideal_mode thm_mem_guest guest);


(* OTHER SI *)
val other_condition = ``si_other_pre_condition 
      (\x:bool[32]. (x <> 0xEF000000w /\ x <> 0xEF000001w))``;
val other_gen_condition = ``si_other_gen_pre_condition 
      (\x:bool[32]. (x <> 0xEF000000w /\ x <> 0xEF000001w))``;
val mode_value = ``19w:bool[5]``;
val (thm_simp, thm_ideal_mode, thm_mem_guest, mem_condition_thm,
     rsa, thm)
  = si_generate_full_precondition ``19w:bool[5]`` other_condition other_gen_condition ;
val pre_with_inv = simp_pre thm_simp mem_condition_thm;

val bap_pre = convert_to_bap_condition(concl pre_with_inv);
val path = "/NOBACKUP/workspaces/robertog/holmodel/verification/out/from_hol2/";
val pre_name = String.concat [path,"other_si", ".pre.il"];
val _ = save_bap_condition bap_pre pre_name;


(* undefined *)
val other_condition = ``\x:composite_arm_state. T``;
val mode_value = ``27w:bool[5]``;

val (thm_simp, thm_ideal_mode, thm_mem_guest,
     rsa, thm)
  = new_gen_precondition mode_value other_condition;
val pre_with_inv = simp_pre thm_simp (ASSUME ``T``);

val bap_pre = convert_to_bap_condition(concl pre_with_inv);
val path = "/NOBACKUP/workspaces/robertog/holmodel/verification/out/from_hol2/";
val pre_name = String.concat [path,"undefined", ".pre.il"];
val _ = save_bap_condition bap_pre pre_name;

val guest = ``guest1``;
save_all "undefined" (generate thm thm_ideal_mode thm_mem_guest guest);

(* prefetch *)
val other_condition = ``\x:composite_arm_state. T``;
val mode_value = ``23w:bool[5]``;

val (thm_simp, thm_ideal_mode, thm_mem_guest,
     rsa, thm)
  = new_gen_precondition mode_value other_condition;
val pre_with_inv = simp_pre thm_simp (ASSUME ``T``);

val bap_pre = convert_to_bap_condition(concl pre_with_inv);
val path = "/NOBACKUP/workspaces/robertog/holmodel/verification/out/from_hol2/";
val pre_name = String.concat [path,"prefetch", ".pre.il"];
val _ = save_bap_condition bap_pre pre_name;

val guest = ``guest1``;
save_all "prefetch" (generate thm thm_ideal_mode thm_mem_guest guest);

(* cswitch *)
val other_condition = ``\is:composite_arm_state.
    ~is.logical_component.box_full2 \/
    ~is.logical_component.ready2
``;
val mode_value = ``18w:bool[5]``;
val (thm_simp, thm_ideal_mode, thm_mem_guest, rsa, thm)
  = new_gen_precondition mode_value other_condition;
val pre_with_inv = simp_pre thm_simp (ASSUME ``T``);

val bap_pre = convert_to_bap_condition(concl pre_with_inv);
val path = "/NOBACKUP/workspaces/robertog/holmodel/verification/out/from_hol2/";
val pre_name = String.concat [path,"cswitch", ".pre.il"];
val _ = save_bap_condition bap_pre pre_name;

save_all "cswitch" (generate thm thm_ideal_mode thm_mem_guest ``guest2``);

(* receive *)
val other_condition = ``\is:composite_arm_state.
    is.logical_component.box_full2 /\
    is.logical_component.ready2
``;
val mode_value = ``18w:bool[5]``;
val (thm_simp, thm_ideal_mode, thm_mem_guest, rsa, thm)
  = new_gen_precondition mode_value other_condition;
val pre_with_inv = simp_pre thm_simp (ASSUME ``T``);

val bap_pre = convert_to_bap_condition(concl pre_with_inv);
val path = "/NOBACKUP/workspaces/robertog/holmodel/verification/out/from_hol2/";
val pre_name = String.concat [path,"receive", ".pre.il"];
val _ = save_bap_condition bap_pre pre_name;

save_all "receive" (generate thm thm_ideal_mode thm_mem_guest ``guest2``);

val thms_const_to_eval = List.tabulate(
(List.length hypervisor_constants_axioms),
(fn thm_id => 
		  ((concat ["hy_cons_th_", Int.toString thm_id]),
		   List.nth (hypervisor_constants_axioms, thm_id)))
	       
);
val _ = computeLib.add_persistent_funs thms_const_to_eval;



val guest = ``guest2``;
save_all "receive" (generate thm thm_ideal_mode thm_mem_guest guest);

val goals = send_generate_full_postcondition thm
    thm_ideal_mode thm_mem_guest guest;
val g1 = List.nth (goals, 14);
val new_state = snd (dest_comb (snd g1));

val hyps = 
    List.filter
	(match_with_constants [``mmu_boot_setup``]
				   ``mmu_boot_setup a ``)
	(CONJUNCTS thm_simp);
val old_setup = List.nth (hyps, 1);
val old_state = snd (dest_comb (concl old_setup));

val new_goal = ``(boot_pt_unchanged ^old_state ^new_state)``;

g `^(hd (fst g1)) ==> ^(new_goal) ==> ^(snd g1)`;
e DISCH_TAC;
e (SIMP_TAC (srw_ss()) []);
e DISCH_TAC;
e (ASSUME_TAC old_setup);

val new_thm = (SIMP_RULE (srw_ss()) []
		  (SPEC new_state (SPEC old_state  mmu_if_mem_unchanged)));

e (ACCEPT_TAC (UNDISCH_ALL new_thm));


EVAL_TAC ([], new_goal);

(* old stuff *)

fun change_guest_memory_prop pres posts =
    let val origin_mem_goal = extract_from_goals 
				  posts
				  is_real_mem_eq_ideal_mem_term
	val (mem_eq_hy, mem_eq_res) = origin_mem_goal
	val new_predicate = ``∀a:bool[32].
    (a ≤ 0x1FFFFFw ∧ a ≥ 0x100000w ⇒ (((mem_rl2 a):bool[8]) = mem_rl1 a)) ∧
    (a ≤ 0x2FFFFFw ∧ a ≥ 0x200000w ⇒ (mem_rl2 a = mem_rl1 a))``
	val goal1 = (
	new_predicate::	mem_eq_hy,
	mem_eq_res
	);
	val mem_eq_pre = extract_real_mem_eq_ideal_mem pres;
	val (g1::[], _) = (ASSUME_TAC mem_eq_pre) goal1;
	val ([], _) = (FULL_SIMP_TAC (srw_ss()) []) g1;
	val posts1 = discharge_from_goals posts origin_mem_goal;
    in
	(mem_eq_hy, new_predicate)::posts1
    end;

fun f handler_name pres hyp =
  let val (posts, state) = send_generate_full_postcondition pres hyp;
      val posts1 = posts@[([], (gen_hol_invariant state))]
      val posts2 = map (
	     fn goal =>
		let val (goal1::[], _ ) =
			(SIMP_TAC (bool_ss)
				  hypervisor_constants_axioms) goal
		in
		    standard_simp_tac goal1
		end
	     ) posts1;
      val posts3 = change_guest_memory_prop pres posts2
      val path =
  "/NOBACKUP/workspaces/robertog/holmodel/verification/out/from_hol2/";
  in
	  map (
	  fn (id, post_bap) =>
	     save_bap_condition post_bap (String.concat
					      [path ,handler_name, ".post.",
					       Int.toString id,
					       ".il"])
	  )
	      (combine (
	       (List.tabulate(List.length posts3, fn x => x)) ,
	       (map (fn (h,t) => convert_to_bap_condition t) posts3)
	      ))
  end;

f();


val (pres, s1, hyp) = si_generate_full_precondition
 ``\x:bool[32]. (x = 0xEF000000w)``;
val pres1 = discard_real_mem_eq_ideal_mem pres;
val inv = ASSUME (gen_hol_invariant s1);
val pre_with_inv = LIST_CONJ (pres1 @ [inv]);
val pre_add = SIMP_RULE (bool_ss) hypervisor_constants_axioms pre_with_inv;
val pre_end = standard_simplification pre_add;
val bap_pre = convert_to_bap_condition(concl pre_end);
val path = "/NOBACKUP/workspaces/robertog/holmodel/verification/out/from_hol2/";
val pre_name = String.concat [path,"release", ".pre.il"];
val _ = save_bap_condition bap_pre pre_name;

f "release" pres hyp;






(* working_directory := "/tmp/"; *)
(* lift_instruction "ea000059"; (* b 170 <impl_undef> *) *)
(* cmd_cntr  := 0x4; *)

cmd_cntr  := 0x50;
lift_instruction "e14fc000"; (* mrs r12, SPSR *)

cmd_cntr  := 0xac;
lift_instruction "e1b0f00e"; (* movs r15, r14 *)

cmd_cntr  := 0xa0;
lift_instruction "e169f000"; (* msr SPSR_fc, r0 *)

(* cmd_cntr  := 0x30c; *)
(* lift_instruction "e3500000"; (* cmp r0, #0 *) *)


val machine_code = "e169f000";
val machine_code = "e14fc000";
val command = armLib.arm_disassemble_decode machine_code;


val command = "mrs r12, spsr_fsxc";
val command = "msr spsr_fsxc, r0";

val command = "mov r0, #0";

val old_state = build_sym_state();
val states = states_from_instruction command;
val (cond, state_if) = hd states;
val state_if_side_effects = lift_flag_effects old_state state_if;
val flags_cpsr = lift_flag_effects_single_psr old_state state_if
					      (``CPSR``, "");

val cpsr = read_psr state_if  ``CPSR``;
val old_cpsr = read_psr old_state  ``CPSR``;
val updated_flags = filter (flag_changed old_cpsr cpsr var_prefix) std_flag_list;



val machine_code = "01a0f00e"; (* moveq r15, r14 *)
val command = armLib.arm_disassemble_decode machine_code;

val command = "pop {r4, pc}";
cmd_cntr  := 0x318;
val old_state = build_sym_state();
val states = states_from_instruction command;
List.length states;
val (cond, state_if) = hd states;
val pc_if = read_reg state_if "pc";
val state_if_side_effects = lift_side_effects old_state state_if;
val (reg_up1, reg_up2) = lift_reg_effects state_if;
val j_pc_if =  pc_frm pc_if state_if "s";
val j_pc_if =  pc_frm pc_if state_if "n";

val pc_pre = !cmd_cntr;
val pc_term = numSyntax.term_of_int pc_pre;
val exp = pc_if;
val pc_num = my_eval ``let pc=((n2w(^pc_term)):bool[32]) in
			   w2n ^exp``;


cmd_cntr  := 0x314;
lift_instruction "01a0f00e"; (* moveq r15, r14 *)



g `^(concl thm) ==>
  (^mem_property (read_mem32 ((lr_svc_rl1:bool[32]) -4w) mem_rl1))`;
e DISCH_TAC;
e (SIMP_TAC (srw_ss()) []);
e (ASSUME_TAC (SIMP_RULE (srw_ss()) [] thm_mem_guest));

e (SUBGOAL_THEN
       ``
  read_mem32 ((lr_svc_rl1:bool[32]) -4w) mem_rl1 =
  read_mem32 ((lr_svc_ila:bool[32]) -4w) mem_ila
        ``
       (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [] thm)
		  THEN FULL_SIMP_TAC (bool_ss) []
));

val lr_svc_rl_eq_id_thm =
    (List.filter (match_with_constants [``lr_svc_rl1:bool[32]``]
				       ``lr_svc_rl1:bool[32] = v``)
		 (BODY_CONJUNCTS thm_simp));

e (REWRITE_TAC lr_svc_rl_eq_id_thm);


e (SUBGOAL_THEN
       ``lr_svc_rl1 = lr_svc_ia1``
       (fn thm => ASSUME_TAC thm));

e (ASSUME_TAC thm_simp);

e RES_TAC;

e (FULL_SIMP_TAC (bool_ss) []);


mem_eq_thm;

read_mem32 (lr_svc_rl1 + 0xFFFFFFFCw) mem_rl1 = 0xEF000001w

(* subgoal *)
e (SIMP_TAC (srw_ss()) []);
e (ACCEPT_TAC thm_mem_guest);




val (imp_ip_1, _) = dest_imp (concl
 (hd (CONJUNCTS (SPEC ``lr_svc_rl1:bool[32]-1w`` mem_eq_thm))));


g `^term_mem_real`;

MAP_EVERY (fn thm => (ASSUME_TAC (UNDISCH thm))) thm_hyp
