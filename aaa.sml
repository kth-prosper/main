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
ASSUME ``(m_rl2:bool[5] = 16w) ��� (m_ila:bool[5] = 16w) ���
	  (m_ilb:bool[5] = 16w)``,
ASSUME ``it_rl2:bool[8] = it_ila:bool[8]``,
ASSUME ``ge_rl2:bool[4] = ge_ila:bool[4]``
]
(ASSUME post_end));

val (_, pre_fix) =dest_thm (SIMP_RULE (bool_ss) [
ASSUME ``(m_rl1:bool[5] = 16w) ��� (m_ila:bool[5] = 16w) ���
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



val pre_forall = ``(���a.
         (a ��� 0x1FFFFFw ��� a ��� 0x100000w ��� ((mem_rl1:bool[32]->bool[8]) a =
					   (mem_ila:bool[32]->bool[8]) a)) ���
         (a ��� 0x2FFFFFw ��� a ��� 0x200000w ��� ((mem_rl1:bool[32]->bool[8]) a =
					   (mem_ilb:bool[32]->bool[8]) a)))``;
val post_forall = ``(���a.
         (a ��� 0x1FFFFFw ��� a ��� 0x100000w ��� ((mem_rl2:bool[32]->bool[8]) a =
					   (mem_ila:bool[32]->bool[8]) a)) ���
         (a ��� 0x2FFFFFw ��� a ��� 0x200000w ��� ((mem_rl2:bool[32]->bool[8]) a =
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







val post = `` (���a.
      (a ��� 0x1FFFFFw ��� a ��� 0x100000w ��� (mem_rl2 :(bool[32] -> bool[8]) a = mem_ila a)) ���
      (a ��� 0x2FFFFFw ��� a ��� 0x200000w ��� (mem_rl2 a = mem_ilb a))) ���
   ((m_rl1 = m_ila ) ��� (m_ilb = 16w)) ���
   ((read_mem32 32896w (mem_rl1:(bool[32] -> bool[8])) = 32900w) ���
    (((N_rl1 ��� N_ila) ��� (Z_rl1 ��� Z_ila))))``;


val pre = `` (���a.
      (a ��� 0x1FFFFFw ��� a ��� 0x100000w ��� (mem_rl1:(bool[32] -> bool[8]) a = mem_ila a)) ���
      (a ��� 0x2FFFFFw ��� a ��� 0x200000w ��� (mem_rl1 a = mem_ilb a))) ���
   ((m_rl1 = m_ila) ��� (m_ilb = 16w)) ���
   ((read_mem32 32896w mem_rl1 = 32900w) ���
    (((N_rl1 ��� N_ila) ��� (Z_rl1 ��� Z_ila))))``;


val post1 = ``
(���(a :bool[32]).
     (a ��� (0x1FFFFFw :bool[32]) ��� a ��� (0x100000w :bool[32]) ���
      ((mem_rl2 :bool[32] -> bool[8]) a =
       (mem_rl1 :bool[32] -> bool[8]) a)) ���
     (a ��� (0x2FFFFFw :bool[32]) ��� a ��� (0x200000w :bool[32]) ���
      (mem_rl2 a = (mem_rl1 :bool[32] -> bool[8]) a))) ���
  ((m_rl2 :bool[5]) = (16w :bool[5])) ���
  ((m_ila :bool[5]) = (16w :bool[5])) ���
  ((m_ilb :bool[5]) = (16w :bool[5])) ���
  ((read_mem32 (32896w :bool[32]) mem_rl2 = (32900w :bool[32])) ���
   ((((N_rl2 :bool) ��� (N_ila :bool)) ��� ((Z_rl2 :bool) ��� (Z_ila :bool)) ���
     ((C_rl2 :bool) ��� (C_ila :bool)) ���
     ((rV_rl2 :bool) ��� (rV_ila :bool)) ���
     ((Q_rl2 :bool) ��� (Q_ila :bool)) ���
     ((it_rl2 :bool[8]) = (it_ila :bool[8])) ���
     ((J_rl2 :bool) ��� (J_ila :bool)) ���
     ((res_rl2 :bool[4]) = (res_ila :bool[4])) ���
     ((ge_rl2 :bool[4]) = (ge_ila :bool[4])) ���
     ((E_rl2 :bool) ��� (E_ila :bool)) ��� ((A_rl2 :bool) ��� (A_ila :bool)) ���
     ((I_rl2 :bool) ��� (I_ila :bool)) ��� ((F_rl2 :bool) ��� (F_ila :bool)) ���
     ((T_rl2 :bool) ��� (T_ila :bool)) ��� (m_rl2 = m_ila)) ���
    ((r0_rl2 :bool[32]) = (r0_ila :bool[32])) ���
    ((r1_rl2 :bool[32]) = (r1_ila :bool[32])) ���
    ((r2_rl2 :bool[32]) = (r2_ila :bool[32])) ���
    ((r3_rl2 :bool[32]) = (r3_ila :bool[32])) ���
    ((r4_rl2 :bool[32]) = (r4_ila :bool[32])) ���
    ((r5_rl2 :bool[32]) = (r5_ila :bool[32])) ���
    ((r6_rl2 :bool[32]) = (r6_ila :bool[32])) ���
    ((r7_rl2 :bool[32]) = (r7_ila :bool[32])) ���
    ((r8_rl2 :bool[32]) = (r8_ila :bool[32])) ���
    ((r9_rl2 :bool[32]) = (r9_ila :bool[32])) ���
    ((r10_rl2 :bool[32]) = (r10_ila :bool[32])) ���
    ((r11_rl2 :bool[32]) = (r11_ila :bool[32])) ���
    ((r12_rl2 :bool[32]) = (r12_ila :bool[32])) ���
    ((sp_rl2 :bool[32]) = (sp_ila :bool[32])) ���
    ((lr_rl2 :bool[32]) = (lr_ila :bool[32])) ���
    ((pc_rl2 :bool[32]) = (pc_ila :bool[32]) + (4w :bool[32]))) ���
   ((((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (31 :num))
        :bool) ��� (N_ilb :bool)) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (30 :num))
        :bool) ��� (Z_ilb :bool)) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (29 :num))
        :bool) ��� (C_ilb :bool)) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (28 :num))
        :bool) ��� (rV_ilb :bool)) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (27 :num))
        :bool) ��� (Q_ilb :bool)) ���
    ((((((15 :num) >< (10 :num))
          (read_mem32
             (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
             mem_rl2) :bool[6]) @@
       (((26 :num) >< (25 :num))
          (read_mem32
             (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
             mem_rl2) :bool[2]))
        :bool[8]) =
     (it_ilb :bool[8])) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (24 :num))
        :bool) ��� (J_ilb :bool)) ���
    ((((23 :num) >< (20 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
           mem_rl2) :bool[4]) =
     (res_ilb :bool[4])) ���
    ((((19 :num) >< (16 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
           mem_rl2) :bool[4]) =
     (ge_ilb :bool[4])) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (9 :num))
        :bool) ��� (E_ilb :bool)) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (8 :num))
        :bool) ��� (A_ilb :bool)) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (7 :num))
        :bool) ��� (I_ilb :bool)) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (6 :num))
        :bool) ��� (F_ilb :bool)) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (5 :num))
        :bool) ��� (T_ilb :bool)) ���
    ((((4 :num) >< (0 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
           mem_rl2) :bool[5]) =
     m_ilb)) ���
   (read_mem32 (read_mem32 (0x181ACw :bool[32]) mem_rl2) mem_rl2 =
    (r0_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (4w :bool[32]))
      mem_rl2 =
    (r1_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (8w :bool[32]))
      mem_rl2 =
    (r2_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (12w :bool[32]))
      mem_rl2 =
    (r3_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (16w :bool[32]))
      mem_rl2 =
    (r4_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (20w :bool[32]))
      mem_rl2 =
    (r5_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (24w :bool[32]))
      mem_rl2 =
    (r6_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (28w :bool[32]))
      mem_rl2 =
    (r7_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (32w :bool[32]))
      mem_rl2 =
    (r8_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (36w :bool[32]))
      mem_rl2 =
    (r9_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (40w :bool[32]))
      mem_rl2 =
    (r10_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (44w :bool[32]))
      mem_rl2 =
    (r11_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (48w :bool[32]))
      mem_rl2 =
    (r12_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (52w :bool[32]))
      mem_rl2 =
    (sp_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (56w :bool[32]))
      mem_rl2 =
    (lr_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (60w :bool[32]))
      mem_rl2 =
    (pc_ilb :bool[32]))) ���
  (read_mem32 (32896w :bool[32]) mem_rl2 = (32900w :bool[32])) ���
  (read_mem32 (33212w :bool[32]) mem_rl2 = (msg11 :bool[32])) ���
  (read_mem32 (0x181B8w :bool[32]) mem_rl2 = r0_ila)``;


val pre1 = ``
   (((m_rl1 :bool[5]) = (m_ila :bool[5])) ���
   ((m_ilb :bool[5]) = (16w :bool[5]))) ���
  ((read_mem32 (32896w :bool[32]) mem_rl1 = (32900w :bool[32])) ���
   ((((N_rl1 :bool) ��� (N_ila :bool)) ��� ((Z_rl1 :bool) ��� (Z_ila :bool)) ���
     ((C_rl1 :bool) ��� (C_ila :bool)) ���
     ((rV_rl1 :bool) ��� (rV_ila :bool)) ���
     ((Q_rl1 :bool) ��� (Q_ila :bool)) ���
     ((it_rl1 :bool[8]) = (it_ila :bool[8])) ���
     ((J_rl1 :bool) ��� (J_ila :bool)) ���
     ((res_rl1 :bool[4]) = (res_ila :bool[4])) ���
     ((ge_rl1 :bool[4]) = (ge_ila :bool[4])) ���
     ((E_rl1 :bool) ��� (E_ila :bool)) ��� ((A_rl1 :bool) ��� (A_ila :bool)) ���
     ((I_rl1 :bool) ��� (I_ila :bool)) ��� ((F_rl1 :bool) ��� (F_ila :bool)) ���
     ((T_rl1 :bool) ��� (T_ila :bool)) ��� (m_rl1 = m_ila)) ���
    ((r0_rl1 :bool[32]) = (r0_ila :bool[32])) ���
    ((r1_rl1 :bool[32]) = (r1_ila :bool[32])) ���
    ((r2_rl1 :bool[32]) = (r2_ila :bool[32])) ���
    ((r3_rl1 :bool[32]) = (r3_ila :bool[32])) ���
    ((r4_rl1 :bool[32]) = (r4_ila :bool[32])) ���
    ((r5_rl1 :bool[32]) = (r5_ila :bool[32])) ���
    ((r6_rl1 :bool[32]) = (r6_ila :bool[32])) ���
    ((r7_rl1 :bool[32]) = (r7_ila :bool[32])) ���
    ((r8_rl1 :bool[32]) = (r8_ila :bool[32])) ���
    ((r9_rl1 :bool[32]) = (r9_ila :bool[32])) ���
    ((r10_rl1 :bool[32]) = (r10_ila :bool[32])) ���
    ((r11_rl1 :bool[32]) = (r11_ila :bool[32])) ���
    ((r12_rl1 :bool[32]) = (r12_ila :bool[32])) ���
    ((sp_rl1 :bool[32]) = (sp_ila :bool[32])) ���
    ((lr_rl1 :bool[32]) = (lr_ila :bool[32])) ���
    ((pc_rl1 :bool[32]) = (pc_ila :bool[32]))) ���
   ((((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (31 :num))
        :bool) ��� (N_ilb :bool)) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (30 :num))
        :bool) ��� (Z_ilb :bool)) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (29 :num))
        :bool) ��� (C_ilb :bool)) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (28 :num))
        :bool) ��� (rV_ilb :bool)) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (27 :num))
        :bool) ��� (Q_ilb :bool)) ���
    ((((((15 :num) >< (10 :num))
          (read_mem32
             (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
             mem_rl1) :bool[6]) @@
       (((26 :num) >< (25 :num))
          (read_mem32
             (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
             mem_rl1) :bool[2]))
        :bool[8]) =
     (it_ilb :bool[8])) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (24 :num))
        :bool) ��� (J_ilb :bool)) ���
    ((((23 :num) >< (20 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
           mem_rl1) :bool[4]) =
     (res_ilb :bool[4])) ���
    ((((19 :num) >< (16 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
           mem_rl1) :bool[4]) =
     (ge_ilb :bool[4])) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (9 :num))
        :bool) ��� (E_ilb :bool)) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (8 :num))
        :bool) ��� (A_ilb :bool)) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (7 :num))
        :bool) ��� (I_ilb :bool)) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (6 :num))
        :bool) ��� (F_ilb :bool)) ���
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (5 :num))
        :bool) ��� (T_ilb :bool)) ���
    ((((4 :num) >< (0 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
           mem_rl1) :bool[5]) =
     m_ilb)) ���
   (read_mem32 (read_mem32 (0x181ACw :bool[32]) mem_rl1) mem_rl1 =
    (r0_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (4w :bool[32]))
      mem_rl1 =
    (r1_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (8w :bool[32]))
      mem_rl1 =
    (r2_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (12w :bool[32]))
      mem_rl1 =
    (r3_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (16w :bool[32]))
      mem_rl1 =
    (r4_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (20w :bool[32]))
      mem_rl1 =
    (r5_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (24w :bool[32]))
      mem_rl1 =
    (r6_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (28w :bool[32]))
      mem_rl1 =
    (r7_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (32w :bool[32]))
      mem_rl1 =
    (r8_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (36w :bool[32]))
      mem_rl1 =
    (r9_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (40w :bool[32]))
      mem_rl1 =
    (r10_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (44w :bool[32]))
      mem_rl1 =
    (r11_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (48w :bool[32]))
      mem_rl1 =
    (r12_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (52w :bool[32]))
      mem_rl1 =
    (sp_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (56w :bool[32]))
      mem_rl1 =
    (lr_ilb :bool[32])) ���
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (60w :bool[32]))
      mem_rl1 =
    (pc_ilb :bool[32]))) ���
  (read_mem32 (32896w :bool[32]) mem_rl1 = (32900w :bool[32])) ���
  (read_mem32 (33212w :bool[32]) mem_rl1 = (msg11 :bool[32])) ���
  (read_mem32 (0x181B8w :bool[32]) mem_rl1 = (msg21 :bool[32]))``;

g ` (^pre1 ==> ^post1) ==>
 ((^pre' ==> ^post'))`;
