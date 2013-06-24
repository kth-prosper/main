use "robertogconf.sml";
use "hol_bap_deps.sml";
use "hol-bap.sml";


cmd_cntr  := 0x0;
lift_instruction "ea0002ca"; (* b b30 <impl_reset> *)

cmd_cntr  := 0xa0;
lift_instruction "e16ff000"; (* msr SPSR_fsxc, r0 *)

cmd_cntr  := 0xe4;
lift_instruction "e14fc000"; (* mrs r12, SPSR *)

cmd_cntr  := 0xa84;
lift_instruction "e1b0f00e"; (* movs r15, r14 *)

val exp = ``((15 >< 10) r0 @@ (26 >< 25) (r0:bool[32])):bool[8]``;

val thm = ``!x:bool[32].
	 ((15 >< 10) x @@ (26 >< 25) x):bool[8] =
         (n2w (w2n (
         (((15 -- 10) x)) << 2 ‖
         ((26 -- 25) x)
	 ))):bool[8]
``;
val exp2 = snd (dest_eq (concl (SIMP_RULE (srw_ss()) [ASSUME thm] (ASSUME ``ggg_xp=^exp``))));


val exp2 = ``
         (((15 -- 10) (x:bool[32]))) << 2 ‖
         ((26 -- 25) x)
``;
exp2ilexp exp false;


wordsSyntax.is_word_bits ``(((15 >< 10) (x:bool[32])):bool[32])``;
wordsSyntax.mk_word_bits (``1``,``1``, ``a:bool[32]``);

exp2ilexp exp2 false;


val exp = ``if ¬svc_f_flag then svc_f_flag else f_flag``;
snd (dest_eq (concl (SIMP_RULE (srw_ss()) [] (ASSUME ``ggg_xp=^exp``))));
exp2ilexp exp false;

is_comb exp;

type_of (fst (dest_comb (fst(dest_comb exp))));

EVAL ``(RName_case r0_ilb r1_ilb r2_ilb r3_ilb r4_ilb r5_ilb r6_ilb
               r7_ilb r8_ilb r8_fiq_ilb r9_ilb r9_fiq_ilb r10_ilb
               r10_fiq_ilb r11_ilb r11_fiq_ilb r12_ilb r12_fiq_ilb
               sp_ilb sp_fiq_ilb sp_irq_ilb sp_svc_ilb sp_abt_ilb
               sp_und_ilb sp_mon_ilb lr_ilb lr_fiq_ilb lr_irq_ilb
               lr_svc_ilb lr_abt_ilb lr_und_ilb lr_mon_ilb pc_ilb)
            RName_0usr``;



val post = `` (∀a.
      (a ≤ 0x1FFFFFw ∧ a ≥ 0x100000w ⇒ (mem_rl2 :(bool[32] -> bool[8]) a = mem_ila a)) ∧
      (a ≤ 0x2FFFFFw ∧ a ≥ 0x200000w ⇒ (mem_rl2 a = mem_ilb a))) ∧
   ((m_rl1 = m_ila ) ∧ (m_ilb = 16w)) ∧
   ((read_mem32 32896w (mem_rl1:(bool[32] -> bool[8])) = 32900w) ∧
    (((N_rl1 ⇔ N_ila) ∧ (Z_rl1 ⇔ Z_ila))))``;


val pre = `` (∀a.
      (a ≤ 0x1FFFFFw ∧ a ≥ 0x100000w ⇒ (mem_rl1:(bool[32] -> bool[8]) a = mem_ila a)) ∧
      (a ≤ 0x2FFFFFw ∧ a ≥ 0x200000w ⇒ (mem_rl1 a = mem_ilb a))) ∧
   ((m_rl1 = m_ila) ∧ (m_ilb = 16w)) ∧
   ((read_mem32 32896w mem_rl1 = 32900w) ∧
    (((N_rl1 ⇔ N_ila) ∧ (Z_rl1 ⇔ Z_ila))))``;


val post1 = ``
(∀(a :bool[32]).
     (a ≤ (0x1FFFFFw :bool[32]) ∧ a ≥ (0x100000w :bool[32]) ⇒
      ((mem_rl2 :bool[32] -> bool[8]) a =
       (mem_rl1 :bool[32] -> bool[8]) a)) ∧
     (a ≤ (0x2FFFFFw :bool[32]) ∧ a ≥ (0x200000w :bool[32]) ⇒
      (mem_rl2 a = (mem_rl1 :bool[32] -> bool[8]) a))) ∧
  ((m_rl2 :bool[5]) = (16w :bool[5])) ∧
  ((m_ila :bool[5]) = (16w :bool[5])) ∧
  ((m_ilb :bool[5]) = (16w :bool[5])) ∧
  ((read_mem32 (32896w :bool[32]) mem_rl2 = (32900w :bool[32])) ∧
   ((((N_rl2 :bool) ⇔ (N_ila :bool)) ∧ ((Z_rl2 :bool) ⇔ (Z_ila :bool)) ∧
     ((C_rl2 :bool) ⇔ (C_ila :bool)) ∧
     ((rV_rl2 :bool) ⇔ (rV_ila :bool)) ∧
     ((Q_rl2 :bool) ⇔ (Q_ila :bool)) ∧
     ((it_rl2 :bool[8]) = (it_ila :bool[8])) ∧
     ((J_rl2 :bool) ⇔ (J_ila :bool)) ∧
     ((res_rl2 :bool[4]) = (res_ila :bool[4])) ∧
     ((ge_rl2 :bool[4]) = (ge_ila :bool[4])) ∧
     ((E_rl2 :bool) ⇔ (E_ila :bool)) ∧ ((A_rl2 :bool) ⇔ (A_ila :bool)) ∧
     ((I_rl2 :bool) ⇔ (I_ila :bool)) ∧ ((F_rl2 :bool) ⇔ (F_ila :bool)) ∧
     ((T_rl2 :bool) ⇔ (T_ila :bool)) ∧ (m_rl2 = m_ila)) ∧
    ((r0_rl2 :bool[32]) = (r0_ila :bool[32])) ∧
    ((r1_rl2 :bool[32]) = (r1_ila :bool[32])) ∧
    ((r2_rl2 :bool[32]) = (r2_ila :bool[32])) ∧
    ((r3_rl2 :bool[32]) = (r3_ila :bool[32])) ∧
    ((r4_rl2 :bool[32]) = (r4_ila :bool[32])) ∧
    ((r5_rl2 :bool[32]) = (r5_ila :bool[32])) ∧
    ((r6_rl2 :bool[32]) = (r6_ila :bool[32])) ∧
    ((r7_rl2 :bool[32]) = (r7_ila :bool[32])) ∧
    ((r8_rl2 :bool[32]) = (r8_ila :bool[32])) ∧
    ((r9_rl2 :bool[32]) = (r9_ila :bool[32])) ∧
    ((r10_rl2 :bool[32]) = (r10_ila :bool[32])) ∧
    ((r11_rl2 :bool[32]) = (r11_ila :bool[32])) ∧
    ((r12_rl2 :bool[32]) = (r12_ila :bool[32])) ∧
    ((sp_rl2 :bool[32]) = (sp_ila :bool[32])) ∧
    ((lr_rl2 :bool[32]) = (lr_ila :bool[32])) ∧
    ((pc_rl2 :bool[32]) = (pc_ila :bool[32]) + (4w :bool[32]))) ∧
   ((((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (31 :num))
        :bool) ⇔ (N_ilb :bool)) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (30 :num))
        :bool) ⇔ (Z_ilb :bool)) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (29 :num))
        :bool) ⇔ (C_ilb :bool)) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (28 :num))
        :bool) ⇔ (rV_ilb :bool)) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (27 :num))
        :bool) ⇔ (Q_ilb :bool)) ∧
    ((((((15 :num) >< (10 :num))
          (read_mem32
             (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
             mem_rl2) :bool[6]) @@
       (((26 :num) >< (25 :num))
          (read_mem32
             (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
             mem_rl2) :bool[2]))
        :bool[8]) =
     (it_ilb :bool[8])) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (24 :num))
        :bool) ⇔ (J_ilb :bool)) ∧
    ((((23 :num) >< (20 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
           mem_rl2) :bool[4]) =
     (res_ilb :bool[4])) ∧
    ((((19 :num) >< (16 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
           mem_rl2) :bool[4]) =
     (ge_ilb :bool[4])) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (9 :num))
        :bool) ⇔ (E_ilb :bool)) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (8 :num))
        :bool) ⇔ (A_ilb :bool)) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (7 :num))
        :bool) ⇔ (I_ilb :bool)) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (6 :num))
        :bool) ⇔ (F_ilb :bool)) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
         mem_rl2 ' (5 :num))
        :bool) ⇔ (T_ilb :bool)) ∧
    ((((4 :num) >< (0 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (64w :bool[32]))
           mem_rl2) :bool[5]) =
     m_ilb)) ∧
   (read_mem32 (read_mem32 (0x181ACw :bool[32]) mem_rl2) mem_rl2 =
    (r0_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (4w :bool[32]))
      mem_rl2 =
    (r1_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (8w :bool[32]))
      mem_rl2 =
    (r2_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (12w :bool[32]))
      mem_rl2 =
    (r3_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (16w :bool[32]))
      mem_rl2 =
    (r4_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (20w :bool[32]))
      mem_rl2 =
    (r5_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (24w :bool[32]))
      mem_rl2 =
    (r6_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (28w :bool[32]))
      mem_rl2 =
    (r7_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (32w :bool[32]))
      mem_rl2 =
    (r8_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (36w :bool[32]))
      mem_rl2 =
    (r9_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (40w :bool[32]))
      mem_rl2 =
    (r10_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (44w :bool[32]))
      mem_rl2 =
    (r11_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (48w :bool[32]))
      mem_rl2 =
    (r12_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (52w :bool[32]))
      mem_rl2 =
    (sp_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (56w :bool[32]))
      mem_rl2 =
    (lr_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl2 + (60w :bool[32]))
      mem_rl2 =
    (pc_ilb :bool[32]))) ∧
  (read_mem32 (32896w :bool[32]) mem_rl2 = (32900w :bool[32])) ∧
  (read_mem32 (33212w :bool[32]) mem_rl2 = (msg11 :bool[32])) ∧
  (read_mem32 (0x181B8w :bool[32]) mem_rl2 = r0_ila)``;


val pre1 = ``
   (((m_rl1 :bool[5]) = (m_ila :bool[5])) ∧
   ((m_ilb :bool[5]) = (16w :bool[5]))) ∧
  ((read_mem32 (32896w :bool[32]) mem_rl1 = (32900w :bool[32])) ∧
   ((((N_rl1 :bool) ⇔ (N_ila :bool)) ∧ ((Z_rl1 :bool) ⇔ (Z_ila :bool)) ∧
     ((C_rl1 :bool) ⇔ (C_ila :bool)) ∧
     ((rV_rl1 :bool) ⇔ (rV_ila :bool)) ∧
     ((Q_rl1 :bool) ⇔ (Q_ila :bool)) ∧
     ((it_rl1 :bool[8]) = (it_ila :bool[8])) ∧
     ((J_rl1 :bool) ⇔ (J_ila :bool)) ∧
     ((res_rl1 :bool[4]) = (res_ila :bool[4])) ∧
     ((ge_rl1 :bool[4]) = (ge_ila :bool[4])) ∧
     ((E_rl1 :bool) ⇔ (E_ila :bool)) ∧ ((A_rl1 :bool) ⇔ (A_ila :bool)) ∧
     ((I_rl1 :bool) ⇔ (I_ila :bool)) ∧ ((F_rl1 :bool) ⇔ (F_ila :bool)) ∧
     ((T_rl1 :bool) ⇔ (T_ila :bool)) ∧ (m_rl1 = m_ila)) ∧
    ((r0_rl1 :bool[32]) = (r0_ila :bool[32])) ∧
    ((r1_rl1 :bool[32]) = (r1_ila :bool[32])) ∧
    ((r2_rl1 :bool[32]) = (r2_ila :bool[32])) ∧
    ((r3_rl1 :bool[32]) = (r3_ila :bool[32])) ∧
    ((r4_rl1 :bool[32]) = (r4_ila :bool[32])) ∧
    ((r5_rl1 :bool[32]) = (r5_ila :bool[32])) ∧
    ((r6_rl1 :bool[32]) = (r6_ila :bool[32])) ∧
    ((r7_rl1 :bool[32]) = (r7_ila :bool[32])) ∧
    ((r8_rl1 :bool[32]) = (r8_ila :bool[32])) ∧
    ((r9_rl1 :bool[32]) = (r9_ila :bool[32])) ∧
    ((r10_rl1 :bool[32]) = (r10_ila :bool[32])) ∧
    ((r11_rl1 :bool[32]) = (r11_ila :bool[32])) ∧
    ((r12_rl1 :bool[32]) = (r12_ila :bool[32])) ∧
    ((sp_rl1 :bool[32]) = (sp_ila :bool[32])) ∧
    ((lr_rl1 :bool[32]) = (lr_ila :bool[32])) ∧
    ((pc_rl1 :bool[32]) = (pc_ila :bool[32]))) ∧
   ((((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (31 :num))
        :bool) ⇔ (N_ilb :bool)) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (30 :num))
        :bool) ⇔ (Z_ilb :bool)) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (29 :num))
        :bool) ⇔ (C_ilb :bool)) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (28 :num))
        :bool) ⇔ (rV_ilb :bool)) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (27 :num))
        :bool) ⇔ (Q_ilb :bool)) ∧
    ((((((15 :num) >< (10 :num))
          (read_mem32
             (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
             mem_rl1) :bool[6]) @@
       (((26 :num) >< (25 :num))
          (read_mem32
             (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
             mem_rl1) :bool[2]))
        :bool[8]) =
     (it_ilb :bool[8])) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (24 :num))
        :bool) ⇔ (J_ilb :bool)) ∧
    ((((23 :num) >< (20 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
           mem_rl1) :bool[4]) =
     (res_ilb :bool[4])) ∧
    ((((19 :num) >< (16 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
           mem_rl1) :bool[4]) =
     (ge_ilb :bool[4])) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (9 :num))
        :bool) ⇔ (E_ilb :bool)) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (8 :num))
        :bool) ⇔ (A_ilb :bool)) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (7 :num))
        :bool) ⇔ (I_ilb :bool)) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (6 :num))
        :bool) ⇔ (F_ilb :bool)) ∧
    (((read_mem32
         (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
         mem_rl1 ' (5 :num))
        :bool) ⇔ (T_ilb :bool)) ∧
    ((((4 :num) >< (0 :num))
        (read_mem32
           (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (64w :bool[32]))
           mem_rl1) :bool[5]) =
     m_ilb)) ∧
   (read_mem32 (read_mem32 (0x181ACw :bool[32]) mem_rl1) mem_rl1 =
    (r0_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (4w :bool[32]))
      mem_rl1 =
    (r1_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (8w :bool[32]))
      mem_rl1 =
    (r2_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (12w :bool[32]))
      mem_rl1 =
    (r3_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (16w :bool[32]))
      mem_rl1 =
    (r4_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (20w :bool[32]))
      mem_rl1 =
    (r5_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (24w :bool[32]))
      mem_rl1 =
    (r6_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (28w :bool[32]))
      mem_rl1 =
    (r7_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (32w :bool[32]))
      mem_rl1 =
    (r8_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (36w :bool[32]))
      mem_rl1 =
    (r9_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (40w :bool[32]))
      mem_rl1 =
    (r10_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (44w :bool[32]))
      mem_rl1 =
    (r11_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (48w :bool[32]))
      mem_rl1 =
    (r12_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (52w :bool[32]))
      mem_rl1 =
    (sp_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (56w :bool[32]))
      mem_rl1 =
    (lr_ilb :bool[32])) ∧
   (read_mem32
      (read_mem32 (0x181ACw :bool[32]) mem_rl1 + (60w :bool[32]))
      mem_rl1 =
    (pc_ilb :bool[32]))) ∧
  (read_mem32 (32896w :bool[32]) mem_rl1 = (32900w :bool[32])) ∧
  (read_mem32 (33212w :bool[32]) mem_rl1 = (msg11 :bool[32])) ∧
  (read_mem32 (0x181B8w :bool[32]) mem_rl1 = (msg21 :bool[32]))``;

g ` (^pre1 ==> ^post1) ==>
 ((^pre' ==> ^post'))`;



val v1 = ``(RName_case r0_rl1 r1_rl1 r2_rl1 r3_rl1 r4_rl1 r5_rl1 r6_rl1
            r7_rl1 r8_rl1 r8_fiq_rl1 r9_rl1 r9_fiq_rl1 r10_rl1
            r10_fiq_rl1 r11_rl1 r11_fiq_rl1 r12_rl1 r12_fiq_rl1 sp_rl1
            sp_fiq_rl1 sp_irq_rl1 sp_svc_rl1 sp_abt_rl1 sp_und_rl1
            sp_mon_rl1 lr_rl1 lr_fiq_rl1 lr_irq_rl1 lr_svc_rl1
            lr_abt_rl1 lr_und_rl1 lr_mon_rl1 (pc_rl1:bool[32]))``;

val v2 = ``(RName_case r0_aa1 r1_aa1 r2_aa1 r3_aa1 r4_aa1 r5_aa1 r6_aa1
            r7_aa1 r8_aa1 r8_fiq_aa1 r9_aa1 r9_fiq_aa1 r10_aa1
            r10_fiq_aa1 r11_aa1 r11_fiq_aa1 r12_aa1 r12_fiq_aa1 sp_aa1
            sp_fiq_aa1 sp_irq_aa1 sp_svc_aa1 sp_abt_aa1 sp_und_aa1
            sp_mon_aa1 lr_aa1 lr_fiq_aa1 lr_irq_aa1 lr_svc_aa1
            lr_abt_aa1 lr_und_aa1 lr_mon_aa1 (pc_aa1:bool[32]))``;

val goal = ASSUME ``(^v1 = ^v2)``;
val res = LIST_CONJ( map (
  fn rname =>
     let val thm2 = prove (``^rname = ^rname``, METIS_TAC [])
	 val thm3 = MK_COMB (goal, thm2) in
	 EVAL_RULE thm3
     end
)
[``RName_0usr:RName``,  ``RName_1usr:RName``,  ``RName_2usr:RName``,  ``RName_3usr:RName``,  ``RName_4usr:RName``,  ``RName_5usr:RName``,  ``RName_6usr:RName``,  ``RName_7usr:RName``,  ``RName_8usr:RName``,  ``RName_8fiq:RName``,  ``RName_9usr:RName``,  ``RName_9fiq:RName``,  ``RName_10usr:RName``,  ``RName_10fiq:RName``,  ``RName_11usr:RName``,  ``RName_11fiq:RName``,  ``RName_12usr:RName``,  ``RName_12fiq:RName``,  ``RName_SPusr:RName``,  ``RName_SPfiq:RName``,  ``RName_SPirq:RName``,  ``RName_SPsvc:RName``,  ``RName_SPabt:RName``,  ``RName_SPund:RName``,  ``RName_SPmon:RName``,  ``RName_LRusr:RName``,  ``RName_LRfiq:RName``,  ``RName_LRirq:RName``,  ``RName_LRsvc:RName``,  ``RName_LRabt:RName``,  ``RName_LRund:RName``,  ``RName_LRmon:RName``,  ``RName_PC:RName``]);

clear_goal_stack ();
