val outer_user_mode_constraints_def = 
    Define `outer_user_mode_constraints sr si g =
      ((sr.psrs (0, CPSR)).F = F)
/\
     ((si.machine1.psrs (0, CPSR)).F = F)
/\
     ((si.machine2.psrs (0, CPSR)).F = F)
/\
     ((sr.psrs (0, CPSR)).I = F)
/\
     ((si.machine1.psrs (0, CPSR)).I = F)
/\
     ((si.machine2.psrs (0, CPSR)).I = F)
/\
     (si.logical_component.context1.spsr.F = F)
/\
     (si.logical_component.context2.spsr.F = F)
/\
     (si.logical_component.context1.spsr.I = F)
/\
     (si.logical_component.context2.spsr.I = F)
`;


val outer_full_relation_switch_def = Define `
outer_full_relation_switch real ideal real0 ideal0 guest =
    (correct_switched_mode_states
	 real ideal real0 ideal0 guest) /\
    (outer_user_mode_constraints real0 ideal0 guest) /\
    (kth_hyp_invariants real) /\
    (mmu_boot_setup real) /\
    (mmu_boot_setup ideal.machine1) /\
    (mmu_boot_setup ideal.machine2) /\
    (mmu_coprocessor_setup real guest) /\
    (mmu_coprocessor_setup ideal.machine1 guest1) /\
    (mmu_coprocessor_setup ideal.machine2 guest2)
`;

val outer_full_relation_user_def = Define `
outer_full_relation_user real ideal guest =
    (correct_user_mode_states
	 real ideal guest) /\
    (outer_user_mode_constraints real ideal guest) /\
    (kth_hyp_invariants real) /\
    (mmu_boot_setup real) /\
    (mmu_boot_setup ideal.machine1) /\
    (mmu_boot_setup ideal.machine2) /\
    (mmu_coprocessor_setup real guest) /\
    (mmu_coprocessor_setup ideal.machine1 guest1) /\
    (mmu_coprocessor_setup ideal.machine2 guest2)
`;

(* Hyp = P /\ MMU_requirement *)
(* user_mode_thm_def *)
(* Concl: P /\ Untuched *)


(* outer_full_relation_user => P /\ MMU_requirement *)
(* Namely: outer_full_relation_user = P /\ P1 /\ MMU_stuff (<> *)
(* 							 MMU_requirement) *)

(* outer_full_relation_user is an invariant: *)
(* outer_full_relation_user(s) /\ Untuched(s, s') /\ P(s') => *)
(* outer_full_relation_user(s') *)


g `(mmu_coprocessor_setup real guest1 /\ mmu_boot_setup real) ==>
   mmu_requirements real guest1`;
e (computeLib.RESTR_EVAL_TAC [``read_mem32``, ``sd_supports_MMU`` ]);
e (SIMP_TAC (bool_ss) hypervisor_constants_axioms );
e (computeLib.RESTR_EVAL_TAC [``read_mem32``, ``sd_supports_MMU`` ]);
e (SIMP_TAC (bool_ss) hypervisor_guest_mem_axioms );
e (STRIP_TAC);
e (REPEAT GEN_TAC);
val bl1  = blastLib.BBLAST_PROVE (``
     ((add:bool[32]) >>> 20) >=+ 0w /\ ((add:bool[32]) >>> 20) <+
				       4096w``);
e (PAT_ASSUM ``!sdi.P`` (fn thm =>
   ASSUME_TAC bl1
   THEN
   ASSUME_TAC (UNDISCH (SPEC ``(add:bool[32]) >>> 20`` thm))
));

e (FULL_SIMP_TAC (srw_ss()) []);

(* e (Cases_on `add>=+global_guest1_start /\ add<=+global_guest1_end`); *)
e (Cases_on `add>=+0x100000w /\ add<=+0x3fffffw`);

(* e (FULL_SIMP_TAC (srw_ss()) hypervisor_guest_mem_axioms ); *)

val bl21 = blastLib.BBLAST_PROVE (``
(add:bool[32])>=+0x100000w /\
add<=+0x3FFFFFw ==>
add ⋙ 20 ≪ 20 ≥₊ 0x100000w ∧ add ⋙ 20 ≪ 20 ≤₊ 0x3FFFFFw
``);
e (ASSUME_TAC (UNDISCH bl21));

e (FULL_SIMP_TAC (srw_ss()) []);
e (computeLib.RESTR_EVAL_TAC [``read_mem32``, ``sd_supports_MMU`` ]);
e (FULL_SIMP_TAC (srw_ss()) [numeral_bitTheory.iSUC]);
e (computeLib.RESTR_EVAL_TAC [``read_mem32``, ``sd_supports_MMU`` ]);

val bl22 = blastLib.BBLAST_PROVE (``
(3072w && read_mem32 (4w * add ⋙ 20 + 16384w) real.memory) ≫ 10 =
3w && read_mem32 (4w * add ⋙ 20 + 16384w) real.memory ⋙ 10
``);
e (ASSUME_TAC bl22);
e (FULL_SIMP_TAC (srw_ss()) []);

e DISCH_TAC;
val bl23 = blastLib.BBLAST_PROVE (``
(add:bool[32]) ⋙ 20 ≪ 20 ≥₊ 0x100000w ==>
add ⋙ 20 ≪ 20 ≤₊ 0x3FFFFFw ==>
(¬(add ≤₊ 0x6FFFFFw) ∨ ¬(add ≥₊ 0x400000w)) ∧ ¬(add >₊ 0x6FFFFFw) ∧
¬(add <₊ 0x100000w)
``);
e (ASSUME_TAC bl23);
e (FULL_SIMP_TAC (srw_ss()) []);



(* SECOND GUEST MEMORY *)
e (Cases_on `add>=+0x400000w /\ add<=+0x6fffffw`);

(* e (FULL_SIMP_TAC (srw_ss()) hypervisor_guest_mem_axioms ); *)
(* Goal splitted  *)

val bl31 = blastLib.BBLAST_PROVE (``
(add:bool[32])>=+0x400000w /\
add<=+0x6FFFFFw ==>
add ⋙ 20 ≪ 20 ≥₊ 0x400000w ∧ add ⋙ 20 ≪ 20 ≤₊ 0x6FFFFFw
``);
e (ASSUME_TAC (UNDISCH bl31));

e (FULL_SIMP_TAC (srw_ss()) []);
(* 4 subgoals *)

e (computeLib.RESTR_EVAL_TAC [``read_mem32``, ``sd_supports_MMU`` ]);
e (FULL_SIMP_TAC (srw_ss()) []);

e (computeLib.RESTR_EVAL_TAC [``read_mem32``, ``sd_supports_MMU`` ]);
e (FULL_SIMP_TAC (srw_ss()) []);

e (computeLib.RESTR_EVAL_TAC [``read_mem32``, ``sd_supports_MMU`` ]);
e (FULL_SIMP_TAC (srw_ss()) []);

e (computeLib.RESTR_EVAL_TAC [``read_mem32``, ``sd_supports_MMU`` ]);
e (FULL_SIMP_TAC (srw_ss()) []);

(* END SECOND GUEST MEMORY *)
(* HYPER MEMORY *)

val bl41 = blastLib.BBLAST_PROVE (``
  ¬((add:bool[32]) ≥₊ 0x100000w ∧ add ≤₊ 0x3FFFFFw) ==>
  ¬(add ≥₊ 0x400000w ∧ add ≤₊ 0x6FFFFFw) ==>

  (¬(add ⋙ 20 ≪ 20 ≥₊ 0x100000w) ∨ ¬(add ⋙ 20 ≪ 20 ≤₊ 0x3FFFFFw)) ∧
  (¬(add ⋙ 20 ≪ 20 ≥₊ 0x400000w) ∨ ¬(add ⋙ 20 ≪ 20 ≤₊ 0x6FFFFFw))
``);
e (ASSUME_TAC (UNDISCH (UNDISCH bl41)));

e (ASSUM_LIST (fn thms =>
  STRIP_ASSUME_TAC (UNDISCH (List.nth (thms, 3)))
));

e (POP_ASSUM (fn thm =>
  REWRITE_TAC [thm]
));
e (computeLib.RESTR_EVAL_TAC [``read_mem32``, ``sd_supports_MMU`` ]);

val bl42 = blastLib.BBLAST_PROVE (``
(3072w && read_mem32 (4w * add ⋙ 20 + 16384w) real.memory) ≫ 10 =
3w && read_mem32 (4w * add ⋙ 20 + 16384w) real.memory ⋙ 10
``);
e (REWRITE_TAC [bl42]);

e (POP_ASSUM (fn thm =>
  REWRITE_TAC [thm]
));
e (FULL_SIMP_TAC (srw_ss()) []);




(* Theorem for unchanged part of mmu *)
val boot_pt_unchanged_up_to_def = Define `
    boot_pt_unchanged_up_to s1 s2 sd =
    let first_sd = global_flpt_add && (0xFFFFC000w:bool[32]) in 
    (!b. (sd <=+ 4096w /\ (b <+ 4w*sd)) ==> (s2.memory (b+first_sd) = s1.memory (b+first_sd)))
`;

val eq_mem_thm = prove (
``(state2.memory (4w * sdi + 0w + 16384w) =
     state1.memory (4w * sdi +  0w + 16384w)) ==>
   (state2.memory (4w * sdi + 1w + 16384w) =
     state1.memory (4w * sdi + 1w + 16384w)) ==>
   (state2.memory (4w * sdi + 2w + 16384w) =
     state1.memory (4w * sdi + 2w + 16384w)) ==>
   (state2.memory (4w * sdi + 3w + 16384w) =
     state1.memory (4w * sdi + 3w + 16384w)) ==>
   ((read_mem32 (16384w + 4w * sdi) state2.memory) =
    (read_mem32 (16384w + 4w * sdi) state1.memory))
``, EVAL_TAC THEN (FULL_SIMP_TAC (srw_ss()) []));


val locs = List.tabulate (4, fn x=>
		     let val off = wordsSyntax.mk_wordii (x,32) in
			 ``4w*sdi+^off``
		     end
);

val locs_thms = map (
		fn add =>
blastLib.BBLAST_PROVE (``
(max_sdi:bool[32]) <=+ (4096w:bool[32]) ==>
sdi ≥₊ 0w ==> sdi <₊ 4096w ==> sdi <₊ max_sdi ==>
(^add <₊ 4w * max_sdi)
``)
		) locs;

val max_unchanged = prove(``
!max_sdi:bool[32].
max_sdi <=+ 4096w ==>
(mmu_boot_setup_sdi_inv state1 max_sdi) ==>
(boot_pt_unchanged_up_to state1 state2 max_sdi) ==>
(mmu_boot_setup_sdi_inv state2 max_sdi)
``,
   GEN_TAC
   THEN (computeLib.RESTR_EVAL_TAC [``read_mem32``])
   THEN (SIMP_TAC (bool_ss) hypervisor_constants_axioms )
   THEN (SIMP_TAC (bool_ss) hypervisor_guest_mem_axioms )
   THEN (computeLib.RESTR_EVAL_TAC [``read_mem32``])
   THEN (STRIP_TAC)
   THEN (STRIP_TAC)
   THEN (STRIP_TAC)
   THEN (REPEAT GEN_TAC)
   THEN (STRIP_TAC)

   THEN (MAP_EVERY (
   fn thm =>
      ASSUME_TAC (UNDISCH_ALL thm))
   locs_thms)

   THEN  (PAT_ASSUM ``!b.P`` (fn eq_mem_thm =>
      MAP_EVERY (
      fn add =>
	 ASSUME_TAC (
	 UNDISCH_ALL (
	 SPEC add eq_mem_thm)))
      locs
   ))

   THEN  (ASSUME_TAC (UNDISCH_ALL eq_mem_thm))
   THEN  (PAT_ASSUM ``read_mem32 a b = c`` (
   fn thm =>
      REWRITE_TAC [thm]))

   THEN (PAT_ASSUM ``!sdi.P`` (
   fn thm =>
      let val other_state_sdi = (UNDISCH (SPEC ``sdi:bool[32]`` thm)) in
      ASSUME_TAC (LIST_CONJ
	      [ASSUME ``sdi ≥₊ 0w:bool[32]``,
	       ASSUME ``sdi <₊ 4096w:bool[32]``,
	       ASSUME ``sdi <₊ max_sdi:bool[32]``])
      THEN
      ACCEPT_TAC other_state_sdi
      end
)));


(* Theorem to check that the whole memory is unchanged than mmu *)
val boot_pt_unchanged_def = Define `
    boot_pt_unchanged s1 s2 =
    let first_sd = global_flpt_add && (0xFFFFC000w:bool[32]) in 
    (!b. (b<+4w*4096w) ==> (s2.memory (b+first_sd) = s1.memory (b+first_sd)))
`;

val max_unch_since_not_chang_thm = prove (``
   (boot_pt_unchanged state1 state2) ==>
   (boot_pt_unchanged_up_to state1 state2 4096w)``,
    EVAL_TAC THEN (REPEAT STRIP_TAC));


val boot_setup_imp_boot_setup_inv = prove (``
(mmu_boot_setup state1) ==>
(mmu_boot_setup_sdi_inv state1 4096w)
``,
FULL_SIMP_TAC (srw_ss()) [mmu_boot_setup_def, mmu_boot_setup_sdi_inv_def]);

val mmu_if_mem_unchanged = prove (``
! state1 state2.
(mmu_boot_setup state1) ==>
(boot_pt_unchanged state1 state2) ==>
(mmu_boot_setup state2)
``,
  REPEAT (GEN_TAC)
  THEN (REPEAT (STRIP_TAC))
  THEN (ASSUME_TAC (UNDISCH max_unch_since_not_chang_thm))
  THEN (ASSUME_TAC (UNDISCH boot_setup_imp_boot_setup_inv))
  THEN (FULL_SIMP_TAC (srw_ss()) [mmu_boot_setup_def])
  THEN (ASSUME_TAC (
   UNDISCH_ALL (
   SIMP_RULE (srw_ss()) [] (SPEC ``4096w:bool[32]`` max_unchanged)
  )))
  THEN (GEN_TAC)
  THEN (DISCH_TAC)
  THEN (PAT_ASSUM ``mmu_boot_setup_sdi_inv state2 4096w``
   (fn thm =>
      ACCEPT_TAC (
      UNDISCH_ALL (
      SPEC ``sdi:bool[32]`` (
      SIMP_RULE (srw_ss())
		[mmu_boot_setup_sdi_inv_def]
		thm))))));

