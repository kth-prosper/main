use "robertogconf.sml";
use "hol_bap_deps.sml";
use "hol-bap.sml";


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

val (s2, post) = send_gen_hol_postcondition();
val (s1, pre) = send_gen_hol_precondition();

(* Remove the quantification from the precondition *)
val pre' = change_condition_on_imemory pre;
val post' = change_condition_on_imemory post;


clear_goal_stack();
g ` (^pre' ==> ^post') ==> ((^pre ==> ^post))`;
e (FULL_SIMP_TAC (srw_ss()) []);

(* Add the invariants to the conditions *)
val inv_pre = gen_hol_invariant(s1);
val inv_post = gen_hol_invariant(s2);


val new_pre = ``^pre' /\ ^inv_pre``;
val new_post = ``^post' /\ ^inv_post``;


(* Apply all constants obtained by the symbol table *)
val (_, post_add) = dest_thm (SIMP_RULE (bool_ss) hypervisor_constants_axioms (ASSUME ``^new_post``));
val (_, pre_add) = dest_thm (SIMP_RULE (bool_ss) hypervisor_constants_axioms (ASSUME ``^new_pre``));

val (_, pre_end) = dest_thm (computeLib.RESTR_EVAL_RULE [``read_mem32``] (ASSUME pre_add));
val (_, post_end) = dest_thm (computeLib.RESTR_EVAL_RULE [``read_mem32``] (ASSUME post_add));

(* patch the conditions for unsupported flags *)
val (_, post_fix) =dest_thm (SIMP_RULE (bool_ss) [
ASSUME ``(m_rl2:bool[5] = 16w) ‘¡Ä (m_ila:bool[5] = 16w) ‘¡Ä
	  (m_ilb:bool[5] = 16w)``,
ASSUME ``it_rl2:bool[8] = it_ila:bool[8]``,
ASSUME ``ge_rl2:bool[4] = ge_ila:bool[4]``
]
(ASSUME post_end));

val (_, pre_fix) =dest_thm (SIMP_RULE (bool_ss) [
ASSUME ``(m_rl1:bool[5] = 16w) ‘¡Ä (m_ila:bool[5] = 16w) ‘¡Ä
	  (m_ilb:bool[5] = 16w)``,
ASSUME ``it_rl1:bool[8] = it_ila:bool[8]``,
ASSUME ``ge_rl1:bool[4] = ge_ila:bool[4]``
]
(ASSUME pre_end));

(* ******************** *)
(* BAP GENERATION *)
(* ******************** *)
use "holtoil/handlers_bap_cond_generator.sml";

val bap_post = convert_to_bap_condition(post_fix);
save_bap_condition bap_post "/NOBACKUP/workspaces/robertog/holmodel/verification/out/from_hol/si1.post.il";

val bap_pre = convert_to_bap_condition(pre_fix);
save_bap_condition bap_pre "/NOBACKUP/workspaces/robertog/holmodel/verification/out/from_hol/si1.pre.il";


(* Temporary stuff *)
clear_goal_stack();
g `^pre_add`;
e (RW_TAC arith_ss []);


clear_goal_stack();
g `^pre_add ==> ^post_add`;
e (FULL_SIMP_TAC (srw_ss()) []);


SIMP_RULE (arith_ss) [] (ASSUME pre_add);



val pre_forall = ``(’¢Ïa.
         (a ‘¡Ü 0x1FFFFFw ‘¡Ä a ‘¡Ý 0x100000w ’¢Í ((mem_rl1:bool[32]->bool[8]) a =
					   (mem_ila:bool[32]->bool[8]) a)) ‘¡Ä
         (a ‘¡Ü 0x2FFFFFw ‘¡Ä a ‘¡Ý 0x200000w ’¢Í ((mem_rl1:bool[32]->bool[8]) a =
					   (mem_ilb:bool[32]->bool[8]) a)))``;
val post_forall = ``(’¢Ïa.
         (a ‘¡Ü 0x1FFFFFw ‘¡Ä a ‘¡Ý 0x100000w ’¢Í ((mem_rl2:bool[32]->bool[8]) a =
					   (mem_ila:bool[32]->bool[8]) a)) ‘¡Ä
         (a ‘¡Ü 0x2FFFFFw ‘¡Ä a ‘¡Ý 0x200000w ’¢Í ((mem_rl2:bool[32]->bool[8]) a =
					   (mem_ilb:bool[32]->bool[8]) a)))``;

val pre_forall' = change_condition_on_imemory pre_forall;
val post_forall' = change_condition_on_imemory post_forall;

g ` (^pre_forall' ==> ^post_forall') ==> ((^pre_forall ==> ^post_forall))`;
e (FULL_SIMP_TAC (srw_ss()) []);

g ` ((^pre_forall ==> ^post_forall)) ==> (^pre_forall' ==> ^post_forall')`;
e (FULL_SIMP_TAC (srw_ss()) []);




g ` (^pre' ==> ^post') ==> ((^pre ==> ^post))`;




e (REWRITE_TAC  [
ASSUME ``(^pre_forall' ==> ^post_forall') ==> ((^pre_forall ==> ^post_forall))``
]);

e (FULL_SIMP_TAC (bool_ss) [
ASSUME ``(^pre_forall' ==> ^post_forall') ==> ((^pre_forall ==> ^post_forall))``
]);

ASSUME `(^pre_forall' ==> ^post_forall') ==> ((^pre_forall ==> ^post_forall))`;

e (RW_TAC (bool_ss) []);

e (FULL_SIMP_TAC (srw_ss()) []);



e (RW_TAC arith_ss []);
e (FULL_SIMP_TAC (srw_ss()) [
ASSUME ``(^pre_forall' ==> ^post_forall') ==> ((^pre_forall ==> ^post_forall))``
]);

g ` (^pre' ==> ^post')`;
e (SIMP_TAC (bool_ss) []);







val post = `` (’¢Ïa.
      (a ‘¡Ü 0x1FFFFFw ‘¡Ä a ‘¡Ý 0x100000w ’¢Í (mem_rl2 :(bool[32] -> bool[8]) a = mem_ila a)) ‘¡Ä
      (a ‘¡Ü 0x2FFFFFw ‘¡Ä a ‘¡Ý 0x200000w ’¢Í (mem_rl2 a = mem_ilb a))) ‘¡Ä
   ((m_rl1 = m_ila ) ‘¡Ä (m_ilb = 16w)) ‘¡Ä
   ((read_mem32 32896w (mem_rl1:(bool[32] -> bool[8])) = 32900w) ‘¡Ä
    (((N_rl1 ’¢Î N_ila) ‘¡Ä (Z_rl1 ’¢Î Z_ila))))``;


val pre = `` (’¢Ïa.
      (a ‘¡Ü 0x1FFFFFw ‘¡Ä a ‘¡Ý 0x100000w ’¢Í (mem_rl1:(bool[32] -> bool[8]) a = mem_ila a)) ‘¡Ä
      (a ‘¡Ü 0x2FFFFFw ‘¡Ä a ‘¡Ý 0x200000w ’¢Í (mem_rl1 a = mem_ilb a))) ‘¡Ä
   ((m_rl1 = m_ila) ‘¡Ä (m_ilb = 16w)) ‘¡Ä
   ((read_mem32 32896w mem_rl1 = 32900w) ‘¡Ä
    (((N_rl1 ’¢Î N_ila) ‘¡Ä (Z_rl1 ’¢Î Z_ila))))``;


val post1 = ``
(’¢Ï(a :bool[32]).
     (a ‘¡Ü (0x1FFFFFw :bool[32]) ‘¡Ä a ‘¡Ý (0x100000w :bool[32]) ’¢Í
      ((mem_rl2 :bool[32] -> bool[8]) a =
       (mem_rl1 :bool[32] -> bool[8]) a)) ‘¡Ä
     (a ‘¡Ü (0x2FFFFFw :bool[32]) ‘¡Ä a ‘¡Ý (0x200000w :bool[32]) ’¢Í
      (mem_rl2 a = (mem_rl1 :bool[32] -> bool[8]) a))) ‘¡Ä
  ((m_rl2 :bool[5]) = (16w :bool[5])) ‘¡Ä
  ((m_ila :bool[5]) = (16w :bool[5])) ‘¡Ä
  ((m_ilb :bool[5]) = (16w :bool[5])) ‘¡Ä
  ((read_mem32 (32896w :bool[32]) mem_rl2 = (32900w :bool[32])) ‘¡Ä
   ((((N_rl2 :bool) ’¢Î (N_ila :bool)) ‘¡Ä ((Z_rl2 :bool) ’¢Î (Z_ila :bool)) ‘¡Ä
     ((C_rl2 :bool) ’¢Î (C_ila :bool)) ‘¡Ä
     ((rV_rl2 :bool) ’¢Î (rV_ila :bool)) ‘¡Ä
     ((Q_rl2 :bool) ’¢Î (Q_ila :bool)) ‘¡Ä
     ((it_rl2 :bool[8]) = (it_ila :bool[8])) ‘¡Ä
     ((J_rl2 :bool) ’¢Î (J_ila :bool)) ‘¡Ä
     ((res_rl2 :bool[4]) = (res_ila :bool[4])) ‘¡Ä
     ((ge_rl2 :bool[4]) = (ge_ila :bool[4])) ‘¡Ä
     ((E_rl2 :bool) ’¢Î (E_ila :bool)) ‘¡Ä ((A_rl2 :bool) ’¢Î (A_ila :bool)) ‘¡Ä
     ((I_rl2 :bool) ’¢Î (I_ila :bool)) ‘¡Ä ((F_rl2 :bool) ’¢Î (F_ila :bool)) ‘¡Ä
     ((T_rl2 :bool) ’¢Î (T_ila :bool)) ‘¡Ä (m_rl2 = m_ila)) ‘¡Ä
    ((r0_rl2 :bool[32]) = (r0_ila :bool[32])) ‘¡Ä
    ((r1_rl2 :bool[32]) = (r1_ila :bool[32])) ‘¡Ä
    ((r2_rl2 :bool[32]) = (r2_ila :bool[32])) ‘¡Ä
    ((r3_rl2 :bool[32]) = (r3_ila :bool[32])) ‘¡Ä
    ((r4_rl2 :bool[32]) = (r4_ila :bool[32])) ‘¡Ä
    ((r5_rl2 :bool[32]) = (r5_ila :bool[32])) ‘¡Ä
    ((r6_rl2 :bool[32]) = (r6_ila :bool[32])) ‘¡Ä
    ((r7_rl2 :bool[32]) = (r7_ila :bool[32])) ‘¡Ä
    ((r8_rl2 :bool[32]) = (r8_ila :bool[32])) ‘¡Ä
    ((r9_rl2 :bool[32]) = (r9_ila :bool[32])) ‘¡Ä
    ((r10_rl2 :bool[32]) = (r10_ila :bool[32])) ‘¡Ä
    ((r11_rl2 :bool[32]) = (r11_ila :bool[32])) ‘¡Ä
    ((r12_rl2 :bool[32]) = (r12_ila :bool[32])) ‘¡Ä
    ((sp_rl2 :bool[32]) = (sp_ila :bool[32])) ‘¡Ä
    ((lr_rl2 :bool[32]) = (lr_ila :bool[32])) ‘¡Ä
    ((pc_rl2 :bool[32]) = (pc_ila :bool[32]) + (4w :bool[32]))) ‘¡Ä
   ((((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (31 :num))
        :bool) ’¢Î (N_ilb :bool)) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (30 :num))
        :bool) ’¢Î (Z_ilb :bool)) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (29 :num))
        :bool) ’¢Î (C_ilb :bool)) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (28 :num))
        :bool) ’¢Î (rV_ilb :bool)) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (27 :num))
        :bool) ’¢Î (Q_ilb :bool)) ‘¡Ä
    ((((((15 :num) >< (10 :num))
          (read_mem32
             (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
             mem_rl2) :bool[6]) @@
       (((26 :num) >< (25 :num))
          (read_mem32
             (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
             mem_rl2) :bool[2]))
        :bool[8]) =
     (it_ilb :bool[8])) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (24 :num))
        :bool) ’¢Î (J_ilb :bool)) ‘¡Ä
    ((((23 :num) >< (20 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
           mem_rl2) :bool[4]) =
     (res_ilb :bool[4])) ‘¡Ä
    ((((19 :num) >< (16 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
           mem_rl2) :bool[4]) =
     (ge_ilb :bool[4])) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (9 :num))
        :bool) ’¢Î (E_ilb :bool)) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (8 :num))
        :bool) ’¢Î (A_ilb :bool)) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (7 :num))
        :bool) ’¢Î (I_ilb :bool)) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (6 :num))
        :bool) ’¢Î (F_ilb :bool)) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (5 :num))
        :bool) ’¢Î (T_ilb :bool)) ‘¡Ä
    ((((4 :num) >< (0 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
           mem_rl2) :bool[5]) =
     m_ilb)) ‘¡Ä
   (read_mem32 (read_mem32 (0x181ACw :bool[32]) mem_rl2) mem_rl2 =
    (r0_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (4w :bool[32]))
      mem_rl2 =
    (r1_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (8w :bool[32]))
      mem_rl2 =
    (r2_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (12w :bool[32]))
      mem_rl2 =
    (r3_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (16w :bool[32]))
      mem_rl2 =
    (r4_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (20w :bool[32]))
      mem_rl2 =
    (r5_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (24w :bool[32]))
      mem_rl2 =
    (r6_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (28w :bool[32]))
      mem_rl2 =
    (r7_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (32w :bool[32]))
      mem_rl2 =
    (r8_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (36w :bool[32]))
      mem_rl2 =
    (r9_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (40w :bool[32]))
      mem_rl2 =
    (r10_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (44w :bool[32]))
      mem_rl2 =
    (r11_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (48w :bool[32]))
      mem_rl2 =
    (r12_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (52w :bool[32]))
      mem_rl2 =
    (sp_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (56w :bool[32]))
      mem_rl2 =
    (lr_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (60w :bool[32]))
      mem_rl2 =
    (pc_ilb :bool[32]))) ‘¡Ä
  (read_mem32 (32896w :bool[32]) mem_rl2 = (32900w :bool[32])) ‘¡Ä
  (read_mem32 (33212w :bool[32]) mem_rl2 = (msg11 :bool[32])) ‘¡Ä
  (read_mem32 (0x181B8w :bool[32]) mem_rl2 = r0_ila)``;


val pre1 = ``
   (((m_rl1 :bool[5]) = (m_ila :bool[5])) ‘¡Ä
   ((m_ilb :bool[5]) = (16w :bool[5]))) ‘¡Ä
  ((read_mem32 (32896w :bool[32]) mem_rl1 = (32900w :bool[32])) ‘¡Ä
   ((((N_rl1 :bool) ’¢Î (N_ila :bool)) ‘¡Ä ((Z_rl1 :bool) ’¢Î (Z_ila :bool)) ‘¡Ä
     ((C_rl1 :bool) ’¢Î (C_ila :bool)) ‘¡Ä
     ((rV_rl1 :bool) ’¢Î (rV_ila :bool)) ‘¡Ä
     ((Q_rl1 :bool) ’¢Î (Q_ila :bool)) ‘¡Ä
     ((it_rl1 :bool[8]) = (it_ila :bool[8])) ‘¡Ä
     ((J_rl1 :bool) ’¢Î (J_ila :bool)) ‘¡Ä
     ((res_rl1 :bool[4]) = (res_ila :bool[4])) ‘¡Ä
     ((ge_rl1 :bool[4]) = (ge_ila :bool[4])) ‘¡Ä
     ((E_rl1 :bool) ’¢Î (E_ila :bool)) ‘¡Ä ((A_rl1 :bool) ’¢Î (A_ila :bool)) ‘¡Ä
     ((I_rl1 :bool) ’¢Î (I_ila :bool)) ‘¡Ä ((F_rl1 :bool) ’¢Î (F_ila :bool)) ‘¡Ä
     ((T_rl1 :bool) ’¢Î (T_ila :bool)) ‘¡Ä (m_rl1 = m_ila)) ‘¡Ä
    ((r0_rl1 :bool[32]) = (r0_ila :bool[32])) ‘¡Ä
    ((r1_rl1 :bool[32]) = (r1_ila :bool[32])) ‘¡Ä
    ((r2_rl1 :bool[32]) = (r2_ila :bool[32])) ‘¡Ä
    ((r3_rl1 :bool[32]) = (r3_ila :bool[32])) ‘¡Ä
    ((r4_rl1 :bool[32]) = (r4_ila :bool[32])) ‘¡Ä
    ((r5_rl1 :bool[32]) = (r5_ila :bool[32])) ‘¡Ä
    ((r6_rl1 :bool[32]) = (r6_ila :bool[32])) ‘¡Ä
    ((r7_rl1 :bool[32]) = (r7_ila :bool[32])) ‘¡Ä
    ((r8_rl1 :bool[32]) = (r8_ila :bool[32])) ‘¡Ä
    ((r9_rl1 :bool[32]) = (r9_ila :bool[32])) ‘¡Ä
    ((r10_rl1 :bool[32]) = (r10_ila :bool[32])) ‘¡Ä
    ((r11_rl1 :bool[32]) = (r11_ila :bool[32])) ‘¡Ä
    ((r12_rl1 :bool[32]) = (r12_ila :bool[32])) ‘¡Ä
    ((sp_rl1 :bool[32]) = (sp_ila :bool[32])) ‘¡Ä
    ((lr_rl1 :bool[32]) = (lr_ila :bool[32])) ‘¡Ä
    ((pc_rl1 :bool[32]) = (pc_ila :bool[32]))) ‘¡Ä
   ((((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (31 :num))
        :bool) ’¢Î (N_ilb :bool)) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (30 :num))
        :bool) ’¢Î (Z_ilb :bool)) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (29 :num))
        :bool) ’¢Î (C_ilb :bool)) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (28 :num))
        :bool) ’¢Î (rV_ilb :bool)) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (27 :num))
        :bool) ’¢Î (Q_ilb :bool)) ‘¡Ä
    ((((((15 :num) >< (10 :num))
          (read_mem32
             (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
             mem_rl1) :bool[6]) @@
       (((26 :num) >< (25 :num))
          (read_mem32
             (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
             mem_rl1) :bool[2]))
        :bool[8]) =
     (it_ilb :bool[8])) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (24 :num))
        :bool) ’¢Î (J_ilb :bool)) ‘¡Ä
    ((((23 :num) >< (20 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
           mem_rl1) :bool[4]) =
     (res_ilb :bool[4])) ‘¡Ä
    ((((19 :num) >< (16 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
           mem_rl1) :bool[4]) =
     (ge_ilb :bool[4])) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (9 :num))
        :bool) ’¢Î (E_ilb :bool)) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (8 :num))
        :bool) ’¢Î (A_ilb :bool)) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (7 :num))
        :bool) ’¢Î (I_ilb :bool)) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (6 :num))
        :bool) ’¢Î (F_ilb :bool)) ‘¡Ä
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (5 :num))
        :bool) ’¢Î (T_ilb :bool)) ‘¡Ä
    ((((4 :num) >< (0 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
           mem_rl1) :bool[5]) =
     m_ilb)) ‘¡Ä
   (read_mem32 (read_mem32 (0x181ACw :bool[32]) mem_rl1) mem_rl1 =
    (r0_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (4w :bool[32]))
      mem_rl1 =
    (r1_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (8w :bool[32]))
      mem_rl1 =
    (r2_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (12w :bool[32]))
      mem_rl1 =
    (r3_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (16w :bool[32]))
      mem_rl1 =
    (r4_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (20w :bool[32]))
      mem_rl1 =
    (r5_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (24w :bool[32]))
      mem_rl1 =
    (r6_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (28w :bool[32]))
      mem_rl1 =
    (r7_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (32w :bool[32]))
      mem_rl1 =
    (r8_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (36w :bool[32]))
      mem_rl1 =
    (r9_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (40w :bool[32]))
      mem_rl1 =
    (r10_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (44w :bool[32]))
      mem_rl1 =
    (r11_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (48w :bool[32]))
      mem_rl1 =
    (r12_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (52w :bool[32]))
      mem_rl1 =
    (sp_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (56w :bool[32]))
      mem_rl1 =
    (lr_ilb :bool[32])) ‘¡Ä
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (60w :bool[32]))
      mem_rl1 =
    (pc_ilb :bool[32]))) ‘¡Ä
  (read_mem32 (32896w :bool[32]) mem_rl1 = (32900w :bool[32])) ‘¡Ä
  (read_mem32 (33212w :bool[32]) mem_rl1 = (msg11 :bool[32])) ‘¡Ä
  (read_mem32 (0x181B8w :bool[32]) mem_rl1 = (msg21 :bool[32]))``;

g ` (^pre1 ==> ^post1) ==>
 ((^pre' ==> ^post'))`;
