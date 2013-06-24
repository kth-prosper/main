use "outer_full_relation.sml";

val add_inst =
    rhs (concl (SIMP_CONV (srw_ss()) hypervisor_constants_axioms
``(b:bool[32])+ (0xFFFFC000w && global_flpt_add)``));

val unchanged_hyper_mem_def = Define `
unchanged_hyper_mem s1 s2 =
!a. 
(a <+ guest1_min_adr \/ a >+ guest1_max_adr) ==>
(a <+ guest2_min_adr \/ a >+ guest2_max_adr) ==>
(s1.memory(a) = s2.memory(a))
`;

val goal = ``
!s1 s2 .
unchanged_hyper_mem s1 s2 ==>
boot_pt_unchanged s1 s2
``;

fun blast_subst_prove term thms =
    blastLib.BBLAST_PROVE (
    rhs(
    concl (
    SIMP_CONV (srw_ss()) thms term
    )));

fun blast_subst_simp_prove term thms =
    blastLib.BBLAST_PROVE (
    rhs(
    concl (
    SIMP_CONV (bool_ss) thms term
    )));

val g1_thm = blast_subst_prove
``
b <+ 16384w ==>
(^add_inst <+ guest1_min_adr \/
 ^add_inst >+ guest1_max_adr)
``
hypervisor_guest_mem_axioms;

val g2_thm = blast_subst_prove
``
b <+ 16384w ==>
(^add_inst <+ guest2_min_adr \/
 ^add_inst >+ guest2_max_adr)
``
hypervisor_guest_mem_axioms;

(* REAL PROOF *)
val thm_unch_hyper_mem_unchanged_mmu_them = prove (``^goal``,
      (FULL_SIMP_TAC (srw_ss()) [unchanged_hyper_mem_def])
  THEN REPEAT GEN_TAC
  THEN REPEAT DISCH_TAC
  THEN FULL_SIMP_TAC (srw_ss())
     (boot_pt_unchanged_def::
       hypervisor_constants_axioms)
  THEN FULL_SIMP_TAC (srw_ss())
     hypervisor_guest_mem_axioms
  THEN EVAL_TAC
  THEN GEN_TAC
  THEN REPEAT DISCH_TAC
  THEN ASSUME_TAC (UNDISCH g1_thm)
  THEN ASSUME_TAC (UNDISCH g2_thm)
  THEN PAT_ASSUM ``!a.p`` (fn thm =>
   ASSUME_TAC (
   UNDISCH_ALL (SPEC ``^add_inst`` thm)
   )
  )
 THEN (FULL_SIMP_TAC (srw_ss()) [])
);



val goal = 
``!state1 g state2. 
    (∀a.
        (g ≠ guest1 ∧ g ≠ guest2 ⇒
         (state1.memory a = state2.memory a)) ∧
        ((g = guest1) ∧ (a >₊ guest1_max_adr ∨ a <₊ guest1_min_adr) ⇒
         (state1.memory a = state2.memory a)) ∧
        ((g = guest2) ∧ (a >₊ guest2_max_adr ∨ a <₊ guest2_min_adr) ⇒
         (state1.memory a = state2.memory a)))
     ==>
     unchanged_hyper_mem state1 state2``
;

val untouched_unchanged_hyper_mem_thm = prove(goal,
      REPEAT GEN_TAC
 THEN DISCH_TAC
 THEN (FULL_SIMP_TAC (srw_ss()) [unchanged_hyper_mem_def])
 THEN (REPEAT GEN_TAC)
 THEN (REPEAT DISCH_TAC)
 THEN (PAT_ASSUM ``!a.p`` (fn thm=>ASSUME_TAC (SPEC ``a:bool[32]`` thm)))
 THEN (METIS_TAC [])
);


val goal = 
``!state1 g state2. 
    (∀a.
        (g ≠ guest1 ∧ g ≠ guest2 ⇒
         (state1.memory a = state2.memory a)) ∧
        ((g = guest1) ∧ (a >₊ guest1_max_adr ∨ a <₊ guest1_min_adr) ⇒
         (state1.memory a = state2.memory a)) ∧
        ((g = guest2) ∧ (a >₊ guest2_max_adr ∨ a <₊ guest2_min_adr) ⇒
         (state1.memory a = state2.memory a)))
     ==>
     boot_pt_unchanged state1 state2``
;
g `^goal`;
e (METIS_TAC [untouched_unchanged_hyper_mem_thm, thm_unch_hyper_mem_unchanged_mmu_them]);



val general_read_32_eq_mem_thm = prove (
``!s1 s2 a.
    (s1.memory (a + 0w) = s2.memory (a + 0w)) ==>
    (s1.memory (a + 1w) = s2.memory (a + 1w)) ==>
    (s1.memory (a + 2w) = s2.memory (a + 2w)) ==>
    (s1.memory (a + 3w) = s2.memory (a + 3w)) ==>
   ((read_mem32 a s1.memory) = (read_mem32 a s2.memory))
``, EVAL_TAC THEN (FULL_SIMP_TAC (srw_ss()) []));


fun my_single_mem_thm_gen rel_add = 
(
 let val my_thm = prove(
   ``(unchanged_hyper_mem s1 s2) ==>
     ((read_mem32 ^rel_add s2.memory) = (read_mem32 ^rel_add s1.memory))``,
   DISCH_TAC THEN
PAT_ASSUM ``unchanged_hyper_mem s0 s1`` (fn thm =>
  let val addresses = List.tabulate (4, fn x=>
      let val off = wordsSyntax.mk_wordii (x,32) in
	  ``^rel_add+^off``
      end)
      val locs_g1 = List.map (fn add_off=>
      blast_subst_simp_prove
``
(^add_off <+ guest1_min_adr \/
 ^add_off >+ guest1_max_adr)
``
hypervisor_guest_mem_axioms
) addresses
      val locs_g2 = List.map (fn add_off=>
      blast_subst_simp_prove
``
(^add_off <+ guest2_min_adr \/
 ^add_off >+ guest2_max_adr)
``
hypervisor_guest_mem_axioms
) addresses
  in
      MAP_EVERY (ASSUME_TAC) locs_g1
 THEN MAP_EVERY (ASSUME_TAC) locs_g2
 THEN ASSUME_TAC thm
 THEN MAP_EVERY (fn add =>
      ASSUME_TAC (
      UNDISCH_ALL (
      SPEC add (
      SIMP_RULE (srw_ss()) hypervisor_guest_mem_axioms (
      computeLib.RESTR_EVAL_RULE [``read_mem32``] thm
      ))))
 ) addresses
 THEN (ASSUME_TAC (
   UNDISCH_ALL (
   SPECL [``s1:arm_state``, ``s2:arm_state``,
	  rel_add]
	 general_read_32_eq_mem_thm)))
THEN (REWRITE_TAC [
let val mem_thm = UNDISCH_ALL (
   SPECL [``s1:arm_state``, ``s2:arm_state``,
	  rel_add]
	 general_read_32_eq_mem_thm)
    val (a,b) = dest_eq (concl mem_thm)
in
   UNDISCH_ALL(
   SPECL [a,b] (INST_TYPE [alpha |-> ``:bool[32]``] EQ_SYM))
end
])
  end
)) in
     my_thm
 end
)
;



fun find_mem_add term =
    if not(is_comb term) then []
    else let
	    val (a,b) = dest_comb term
	in
	    if not(is_comb a) then (find_mem_add a)@(find_mem_add b)
	    else let
		    val (a1,a2) = dest_comb a
		in
		    if not(is_const a1) then
			(find_mem_add a)@(find_mem_add b)
		    else let
			    val (f_name, f_type) = dest_const a1
			in
		     (* andalso (a1 = ``read_mem32``) *)
			    if (b = ``s2.memory``) andalso (f_name = "read_mem32") then
				[a2]
			    else
				(find_mem_add a)@(find_mem_add b)
			end
		end
	end
;

fun hyper_mem_loc_tac (ass_list, prop) =
    let val mem_locs = find_mem_add prop
    in
	(MAP_EVERY (fn add_loc =>
		       (REWRITE_TAC
			    [UNDISCH (my_single_mem_thm_gen add_loc)])
		   ) mem_locs) (ass_list, prop)
    end;


val goal = ``!s1 s2.
kth_hyp_invariants s1 ==>
unchanged_hyper_mem s1 s2 ==>
kth_hyp_invariants s2
``;

g `^goal`;
e (REPEAT GEN_TAC);
e (REPEAT DISCH_TAC);

e (computeLib.RESTR_EVAL_TAC [``read_mem32``]);

e (
   REPEAT CONJ_TAC
 THEN REPEAT (
      (FULL_SIMP_TAC (srw_ss()) hypervisor_constants_axioms)
 THEN hyper_mem_loc_tac
 THEN (PAT_ASSUM ``kth_hyp_invariants s1`` (fn thm =>
   let val thm1 = 
   SIMP_RULE (srw_ss()) hypervisor_constants_axioms (
   computeLib.RESTR_EVAL_RULE [``read_mem32``] thm
   ) 
       val thm2s = CONJUNCTS thm1
   in
       MAP_EVERY (fn thm_loc => ASSUME_TAC thm_loc) thm2s
   end
))
 THEN (FULL_SIMP_TAC (srw_ss()) []))
);


g `^goal`;
e (REPEAT GEN_TAC
  THEN REPEAT DISCH_TAC
  THEN (computeLib.RESTR_EVAL_TAC [``read_mem32``])
  THEN (FULL_SIMP_TAC (srw_ss()) hypervisor_constants_axioms)
  THEN hyper_mem_loc_tac
  THEN (PAT_ASSUM ``kth_hyp_invariants s1`` (fn thm =>
   let val thm1 = 
   SIMP_RULE (srw_ss()) hypervisor_constants_axioms (
   computeLib.RESTR_EVAL_RULE [``read_mem32``] thm
   ) 
       val thm2s = CONJUNCTS thm1
   in
       MAP_EVERY (fn thm_loc => ASSUME_TAC thm_loc) thm2s
   end
))
  THEN  (FULL_SIMP_TAC (srw_ss()) [])
);





