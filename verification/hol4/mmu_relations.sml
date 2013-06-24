(* =============     Untouched   ==========================*)

val untouched_def = Define `untouched id state1 state2 =
(* foreign registers *)
(!reg pro.  reg NOTIN  {RName_0usr; RName_1usr; RName_2usr; RName_3usr; RName_4usr; RName_5usr;
                       RName_6usr; RName_7usr; RName_8usr; RName_9usr; RName_10usr; RName_11usr;
                       RName_12usr; RName_SPusr; RName_LRusr; RName_PC}
             ==> (state1.registers (pro, reg) = state2.registers (pro, reg)))
/\ 

(* foreign PSR *)
    (!psr pro. ((psr <> CPSR) ==> (state1.psrs (pro, psr) = state2.psrs (pro, psr))))
/\
(* coprocessor registers *)
   (state1.coprocessors.state.cp15.C1 = state2.coprocessors.state.cp15.C1)
/\ (state1.coprocessors.state.cp15.C2 = state2.coprocessors.state.cp15.C2)
/\ (state1.coprocessors.state.cp15.C3 = state2.coprocessors.state.cp15.C3)

/\
(* foreign memory *)
 (! a. 
 (((id <> guest1) /\ (id<>guest2))                             ==>   
        ((state1.memory a) = (state2.memory a)))
 /\
 (((id = guest1) /\ ((a > 0x1FFFFFw) \/ (a < 0x100000w))) ==> 
	((state1.memory a) = (state2.memory a))) 
 /\ 
 (((id = guest2) /\ ((a > 0x2FFFFFw) \/ (a < 0x200000w))) ==>
	((state1.memory a) = (state2.memory a))))
`; 

val untouched_incl_mode_def = Define `untouched_incl_mode id state1 state2 =
                                      (untouched id state1 state2) /\ 
					(ARM_MODE state1 = ARM_MODE state2)`;


val untouching_def = Define `untouching comp =
      !gst s s' a. (mmu_requirements s gst) ==> (comp s = ValueState a s') ==> (untouched gst s s') `;


val untouching_abs_def = Define `untouching_abs f =
      !c gst s s' a. (mmu_requirements s gst) ==> (f c s = ValueState a s') ==> (untouched gst s s')`;


val untouched_trans = store_thm (
    "untouched_trans",
    ``!a b c g. (untouched g a b) ==> (untouched g b c) ==> (untouched g a c)``,
    RW_TAC (srw_ss()) [untouched_def] THEN METIS_TAC []);

val untouched_memory_eq_lem = store_thm(
    "untouched_memory_eq_lem",
    ``!s1 s2 g. (untouched g s1 s2) ==> 
                (!add. (add < 0x100000w) ==> (s1.memory add = s2.memory add))``,
    REPEAT STRIP_TAC
       THEN Cases_on `(g<>guest1) /\ (g<>guest2)` 
       THENL [ALL_TAC, IMP_RES_TAC (blastLib.BBLAST_PROVE ``!(a:word32). (a < 0x100000w) ==> (a < 0x200000w)``)]
       THEN FULL_SIMP_TAC (srw_ss()) [untouched_def]);



val untouched_permissions_lem = store_thm(
    "untouched_permissions_lem",
    ``!s1 s2 g. 
         (mmu_requirements s1 g) ==> 
         (untouched g s1 s2) 
     ==> (!add isw c1 c3 priv. 
          (permitted_byte add isw c1 s1.coprocessors.state.cp15.C2 c3 priv s1.memory 
         = permitted_byte add isw c1 s1.coprocessors.state.cp15.C2 c3 priv s2.memory))``,
    REPEAT STRIP_TAC
       THEN IMP_RES_TAC untouched_memory_eq_lem
       THEN FULL_SIMP_TAC (srw_ss()) [permitted_byte_def]
       THEN UNDISCH_TAC ``mmu_requirements s1 g``
       THEN PURE_ONCE_REWRITE_TAC [mmu_requirements_def]
       THEN STRIP_TAC
       THEN Cases_on `permitted_byte add F s1.coprocessors.state.cp15.C1 s1.coprocessors.state.cp15.C2 s1.coprocessors.state.cp15.C3 F s1.memory`
       THEN Cases_on `r`
       THEN PAT_ASSUM (``!A1 A2 A3 A4 A5. (B ==> C)``) (fn th => (MP_TAC (SPECL [``add:word32``, ``F``,``q:bool``, ``q':bool``, ``r':string``] th))) 
       THEN RW_TAC (srw_ss()) [read_mem32_def]
       THEN `content_of_sd = content_of_sd'` by 
            (UNABBREV_ALL_TAC
                THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF, read_mem32_def] 
                THEN IMP_RES_TAC (blastLib.BBLAST_PROVE ``!(add:word32). ((0xFFFFC000w && s2.coprocessors.state.cp15.C2) >= 0w) ==> ((0xFFFFC000w && s2.coprocessors.state.cp15.C2) < 0x100000w)  ==> ((0xFFFFC000w && s2.coprocessors.state.cp15.C2) + 16383w < 0x100000w) ==> 
     (((0xFFFFC000w && s2.coprocessors.state.cp15.C2) + 4w *(add≫ 20)      < 0x100000w)  /\
     ((0xFFFFC000w && s2.coprocessors.state.cp15.C2) + 4w *(add≫ 20) + 1w < 0x100000w)  /\
     ((0xFFFFC000w && s2.coprocessors.state.cp15.C2) + 4w *(add≫ 20) + 2w < 0x100000w)  /\
     ((0xFFFFC000w && s2.coprocessors.state.cp15.C2) + 4w *(add≫ 20) + 3w < 0x100000w) )``) 
                THEN METIS_TAC [])
       THEN UNABBREV_ALL_TAC
       THEN METIS_TAC []);



val untouched_mmu_setup_lem = store_thm(
    "untouched_mmu_setup_lem",
    ``!s1 s2 g.
          (mmu_requirements s1 g) ==> 
          (untouched g s1 s2)  
        ==> 
          (mmu_requirements s2 g)``,
    REPEAT STRIP_TAC
       THEN IMP_RES_TAC (SPECL [``s1:arm_state``, ``s2:arm_state``, ``g:word32``] untouched_permissions_lem)
       THEN UNDISCH_TAC ``mmu_requirements s1 g``
       THEN FULL_SIMP_TAC (srw_ss()) [untouched_def]
       THEN PURE_ONCE_REWRITE_TAC [mmu_requirements_def]
       THEN METIS_TAC []);


val trivially_untouched_mmu_setup_lem = store_thm(
    "trivially_untouched_mmu_setup_lem",
    ``!s t gst. (s.coprocessors = t.coprocessors) ==> 
                (s.memory = t.memory)             ==>
                (s.accesses = t.accesses)         
       ==> 
      (mmu_requirements s gst = mmu_requirements t gst)``,
    RW_TAC (srw_ss()) [mmu_requirements_def]);


val trivially_untouched_av_lem = store_thm(
    "trivially_untouched_av_lem",
    ``!s t gst. (mmu_requirements s gst)          ==>
                (s.coprocessors = t.coprocessors) ==>
                (s.memory = t.memory)             ==>
                (s.accesses = t.accesses)
       ==> (access_violation s = access_violation t)``,
    REPEAT STRIP_TAC
       THEN `mmu_requirements t gst` by IMP_RES_TAC trivially_untouched_mmu_setup_lem
       THEN IMP_RES_TAC access_violation_req
       THEN RW_TAC (srw_ss()) [access_violation_pure_def]);



(* =============   Similar    ==========================*)

val equal_user_register_def = Define `equal_user_register s t =
(! ii reg.  reg IN  {RName_0usr; RName_1usr; RName_2usr; RName_3usr; RName_4usr; RName_5usr;
                       RName_6usr; RName_7usr; RName_8usr; RName_9usr; RName_10usr; RName_11usr;
                       RName_12usr; RName_SPusr; RName_LRusr; RName_PC}
             ==> (s.registers (ii.proc, reg) = t.registers (ii.proc, reg)))`;



val similar_def = Define `similar s1 s2 =
(! add.
 (((add <= 0x1FFFFFw) /\ (add >= 0x100000w)) ==>
        ((s1.memory add) = (s2.memory add)))
   /\
 (((add <= 0x2FFFFFw) /\ (add >= 0x200000w)) ==>
        ((s1.memory add) = (s2.memory add))))                       /\
(!ii. (s1.psrs (ii.proc,CPSR)= s2.psrs (ii.proc,CPSR)))             /\ 
(equal_user_register s1  s2)      /\
(s1.information = s2.information)                                   /\
(s1.coprocessors.state.cp15 = s2.coprocessors.state.cp15)           /\
(!ii. s1.interrupt_wait ii.proc = s2.interrupt_wait ii.proc)        /\
(access_violation s1 = access_violation s2)
`;


val preserve_relation_mmu_def = Define `preserve_relation_mmu comp invr1 invr2 = 
    !g s1 s2.
    mmu_requirements s1 g                   ==>
    mmu_requirements s2 g                   ==>
    similar s1 s2     
    ==> 
   ((invr1 s1) /\ (invr1 s2)) ==>
    ((?a s1' s2'.((comp s1 = ValueState a s1') /\  
		(comp s2 = ValueState a s2') /\ (similar s1' s2')
/\  (invr2 s1' )  /\  (invr2 s2'))) 
\/   (? e. (comp s1 = Error e) /\ (comp s2 = Error e)))`;


val preserve_relation_mmu_abs_def = Define `preserve_relation_mmu_abs comp invr1 invr2 = 
    !c g s1 s2 .
    mmu_requirements s1 g                   ==>
    mmu_requirements s2 g                   ==>
    similar s1 s2                          
    ==> 
   ((invr1 s1) /\ (invr1 s2)) ==>
    ((?a s1' s2'.((comp c s1 = ValueState a s1') /\  (comp c s2 = ValueState a s2') 
		  /\ (similar s1' s2')/\  (invr2 s1' )  /\  (invr2 s2'))) 
			       \/   (? e. (comp c s1 = Error e) /\ (comp c s2 = Error e)))`;


val SEQT_PRESERVE_TAC = fn F1 =>
    (RW_TAC (srw_ss()) [seqT_def,constT_def,preserve_relation_mmu_def,preserve_relation_mmu_abs_def, untouching_def, comb_def]
       THEN Cases_on [QUOTE (F1^" s1")]
       THEN Cases_on [QUOTE (F1^" s2")]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) [] 
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def]) 
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN RW_TAC (srw_ss()) []
       THEN `mmu_requirements b g` by METIS_TAC [untouched_mmu_setup_lem]
       THEN `mmu_requirements b' g` by METIS_TAC [untouched_mmu_setup_lem]
       THEN METIS_TAC []);

val SEQT_PRESERVE_BEGIN_TAC = fn F1 =>
    (RW_TAC (srw_ss()) [seqT_def,constT_def,preserve_relation_mmu_def,preserve_relation_mmu_abs_def, untouching_def]
       THEN Cases_on [QUOTE (F1^" s1")]
       THEN Cases_on [QUOTE (F1^" s2")]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) [] 
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def]) 
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN RW_TAC (srw_ss()) []
       THEN `mmu_requirements b g` by METIS_TAC [untouched_mmu_setup_lem]
       THEN `mmu_requirements b' g` by METIS_TAC [untouched_mmu_setup_lem]);



val SEQT_UNTOUCHED_TAC =
    UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) [seqT_def, untouching_def]
       THEN UNDISCH_ALL_TAC 
       THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) [])
       THEN UNDISCH_ALL_TAC 
       THEN RW_TAC (srw_ss()) [] 
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN IMP_RES_TAC untouched_mmu_setup_lem
       THEN RES_TAC
       THEN IMP_RES_TAC untouched_trans
       THEN FULL_SIMP_TAC (srw_ss()) [];


val SEQT_PRESERVE_BEGIN_ABS_TAC = fn (F1, C)  =>
    (RW_TAC (srw_ss()) [seqT_def,constT_def,preserve_relation_mmu_def, preserve_relation_mmu_abs_def, untouching_def, untouching_abs_def]
       THEN Cases_on [QUOTE (F1^" s1")]
       THEN Cases_on [QUOTE (F1^" s2")]
       THEN RES_TAC
       THEN REPEAT (PAT_ASSUM ``!(c:num). X`` (fn th => ASSUME_TAC (SPEC C th)))
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) [] 
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def]) 
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN RW_TAC (srw_ss()) []
       THEN `mmu_requirements b g` by METIS_TAC [untouched_mmu_setup_lem]
       THEN `mmu_requirements b' g` by METIS_TAC [untouched_mmu_setup_lem]);


val SEQT_PRESERVE_ABS_TAC = fn (F1, C)  =>
    (RW_TAC (srw_ss()) [seqT_def,constT_def,preserve_relation_mmu_def, preserve_relation_mmu_abs_def, untouching_def, untouching_abs_def]
       THEN Cases_on [QUOTE (F1^" s1")]
       THEN Cases_on [QUOTE (F1^" s2")]
       THEN RES_TAC
       THEN REPEAT (PAT_ASSUM ``!(c:num). X`` (fn th => ASSUME_TAC (SPEC C th)))
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) [] 
       THEN (`access_violation b = access_violation b'` by METIS_TAC [similar_def]) 
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN RW_TAC (srw_ss()) []
       THEN `mmu_requirements b g` by METIS_TAC [untouched_mmu_setup_lem]
       THEN `mmu_requirements b' g` by METIS_TAC [untouched_mmu_setup_lem]
       THEN METIS_TAC []);


val SEQT_UNTOUCHED_TAC =
    UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) [seqT_def, untouching_def, untouching_abs_def]
       THEN UNDISCH_ALL_TAC 
       THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) [])
       THEN UNDISCH_ALL_TAC 
       THEN RW_TAC (srw_ss()) [] 
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN IMP_RES_TAC untouched_mmu_setup_lem
       THEN RES_TAC
       THEN IMP_RES_TAC untouched_trans
       THEN FULL_SIMP_TAC (srw_ss()) [];


val first_abs_lemma = store_thm ("first_abs_lemma",
``(!f g invr. (f=g) ==> ((preserve_relation_mmu f invr) = (preserve_relation_mmu g invr)))``,
 RW_TAC (srw_ss()) []);


val second_abs_lemma = store_thm ("second_abs_lemma",
``! f invr. (! y. preserve_relation_mmu (f y) invr) = preserve_relation_mmu_abs (f) invr``,
 RW_TAC (srw_ss()) [preserve_relation_mmu_def,preserve_relation_mmu_abs_def]);

val first_abs_ut_lemma = store_thm ("first_abs_ut_lemma",
``(!f g. (f=g) ==> ((untouching  f) = (untouching g)))``,
 RW_TAC (srw_ss()) []);


val second_abs_ut_lemma = store_thm ("second_abs_ut_lemma",
``! f . (! y. untouching (f y)) = untouching_abs (f)``,
 RW_TAC (srw_ss()) [untouching_abs_def,untouching_def]);

val seqT_preserves_user_relation_thm = store_thm(
    "seqT_preserves_user_relation_thm",
    ``! f1 f2 invr1 invr2.
          (preserve_relation_mmu f1 invr1 invr1) ==>
          (preserve_relation_mmu_abs f2 invr1 invr1) ==>
          (untouching f1)            
                ==>
          (preserve_relation_mmu (f1 >>= (f2)) invr1 invr1)``,
    SEQT_PRESERVE_TAC "f1");

val seqT_preserves_user_relation_thm = store_thm(
    "seqT_preserves_user_relation_thm",
    ``! f1 f2 invr1 invr2 invr3.
          (preserve_relation_mmu f1 invr1 invr1) ==>
          (preserve_relation_mmu_abs f2 invr1 invr2) ==>
          (untouching f1)            
	  ==> (comb invr1 invr2 invr3)
                ==>
	   (preserve_relation_mmu (f1 >>= (f2)) invr1 invr3)``,
    SEQT_PRESERVE_TAC "f1");

val comb_def = Define `comb invr1 invr2 invr3 = (!s. invr3 s = (invr1 s \/ invr2 s))`;

val seqT_untouching_thm = store_thm(
     "seqT_untouching_thm",
     ``!f g.
       (untouching f) ==>
       (untouching_abs g)
     ==>
       (untouching (f >>= g))``,
     RW_TAC (srw_ss()) [seqT_def, untouching_def, untouching_abs_def]
        THEN Cases_on `f s`
        THEN Cases_on `access_violation b`
        THEN FULL_SIMP_TAC (srw_ss()) []
        THEN IMP_RES_TAC untouched_mmu_setup_lem
        THEN (NTAC 3 RES_TAC)
        THEN IMP_RES_TAC untouched_trans
        THEN FULL_SIMP_TAC (srw_ss()) []);

val parT_preserves_user_relation_thm = store_thm("parT_preserves_user_relation_thm",
  `` ! f1 f2 invr.
	  (preserve_relation_mmu f1 invr) ==>
          (preserve_relation_mmu f2 invr) ==>
          (untouching f1)            
               ==>
           (preserve_relation_mmu (f1 ||| f2) invr) ``,
RW_TAC (srw_ss()) [parT_def]
THEN UNDISCH_ALL_TAC
THEN SEQT_PRESERVE_BEGIN_TAC "f1"
THEN
Cases_on `f2 b`
       THEN Cases_on `f2 b'`
 THEN FULL_SIMP_TAC (srw_ss()) [] 
THEN PAT_ASSUM ``∀g s1 s2.
        mmu_requirements s1 g ⇒
        mmu_requirements s2 g ⇒
        similar s1 s2 ⇒
        invr s1 ⇒
        invr s2 ⇒
        (∃a s1' s2'.
           (f2 s1 = ValueState a s1') ∧
           (f2 s2 = ValueState a s2') ∧ similar s1' s2' ∧ invr s1' ∧ invr s2') ∨
        ∃e.
          (f2 s1 = Error e) ∧
          (f2 s2 = Error e)`` (fn th => ASSUME_TAC (SPECL [``g:word32``, ``b:arm_state``, ``b':arm_state``] th))
THEN RES_TAC
THEN  FULL_SIMP_TAC (srw_ss()) []
THEN REPEAT IF_CASES_TAC THEN RW_TAC (srw_ss()) []
THEN (`access_violation b'' = access_violation b'''` by METIS_TAC [similar_def])
THEN FULL_SIMP_TAC (srw_ss()) [] );

val parT_untouching_thm = store_thm(
     "parT_untouching_thm",
     ``!f1 f2.
       (untouching f1) ==>
       (untouching f2)
     ==>
       (untouching (f1 ||| f2))``,
     REPEAT STRIP_TAC
        THEN RW_TAC arith_ss [parT_def, constT_def]
        THEN SEQT_UNTOUCHED_TAC);


val constT_preserves_user_relation_thm = store_thm("constT_preserves_user_relation_thm",
``!p invr.  (preserve_relation_mmu (constT p) invr) /\ (untouching (constT p))``,
(RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def,constT_def,untouching_def,untouched_def]));


val cond_preserves_user_relation_thm = store_thm("cond_preserves_user_relation_thm",
  ``!p f g. ((preserve_relation_mmu f) /\ (preserve_relation_mmu g)
             /\ (untouching f) /\ (untouching g)) 
	 ==> ((preserve_relation_mmu (if p then f else g))
	         /\
	      (untouching (if p then f else g)))``,(RW_TAC (srw_ss()) []));


val condT_preserves_user_relation_thm = store_thm("condT_preserves_user_relation_thm",
``! b f. ((preserve_relation_mmu f) /\ (untouching  f))
		==> 
         ((preserve_relation_mmu (condT b f )) /\ (untouching (condT b f )))``,
(RW_TAC (srw_ss()) [preserve_relation_mmu_def,condT_def,similar_def,constT_def,untouching_def,untouched_def]));


val parT_untouching_thm = store_thm(
     "parT_untouching_thm",
     ``!f1 f2.
       (untouching f1) ==>
       (untouching f2)
     ==>
       (untouching (f1 ||| f2))``,
     REPEAT STRIP_TAC
        THEN RW_TAC arith_ss [parT_def, constT_def]
        THEN SEQT_UNTOUCHED_TAC);

val forT_untouching_thm = store_thm(
    "forT_untouching_thm",
    ``!f. 
            (untouching_abs (f))
        ==> (!l h. untouching (forT l h f))``,
    REPEAT STRIP_TAC
      THEN Induct_on `h - l` 
      THENL [FULL_SIMP_TAC (srw_ss()) []
                THEN REPEAT STRIP_TAC
                THEN NTAC 2 (PURE_ONCE_REWRITE_TAC [forT_def, LET_DEF])
                THEN RW_TAC arith_ss [untouching_def, untouching_abs_def, constT_def, seqT_def]
                THEN SEQT_UNTOUCHED_TAC
                THEN FULL_SIMP_TAC (srw_ss()) [untouched_def],
             FULL_SIMP_TAC (srw_ss()) []
                THEN REPEAT STRIP_TAC
                THEN PURE_ONCE_REWRITE_TAC [forT_def, LET_DEF]
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC arith_ss [constT_def]
                THEN `v = h - (l+1)` by FULL_SIMP_TAC arith_ss []
                THEN PAT_ASSUM ``!h l. X => Y`` (fn th => IMP_RES_TAC (SPECL [``h:num``, ``(l+1):num``] th))
                THEN SEQT_UNTOUCHED_TAC]);



val forT_preserving_thm = store_thm(
    "forT_preserving_thm",
    ``!f. (untouching_abs (f))            ==>
          (preserve_relation_mmu_abs (f)) 
       ==> 
          (!l h. preserve_relation_mmu (forT l h f))``,
    REPEAT STRIP_TAC
      THEN IMP_RES_TAC forT_untouching_thm
      THEN Induct_on `h - l` 
      THENL [FULL_SIMP_TAC (srw_ss()) []
                THEN (REPEAT STRIP_TAC)
                THEN (NTAC 2 (PURE_ONCE_REWRITE_TAC [forT_def, LET_DEF]))
                THEN RW_TAC arith_ss [preserve_relation_mmu_def, preserve_relation_mmu_abs_def, constT_def, seqT_def]
                THEN (REPEAT STRIP_TAC)
                THEN UNDISCH_ALL_TAC
                THEN SEQT_PRESERVE_ABS_TAC ("f l", ``l:num``),
             FULL_SIMP_TAC (srw_ss()) []
                THEN REPEAT STRIP_TAC
                THEN PURE_ONCE_REWRITE_TAC [forT_def, LET_DEF]
                THEN UNDISCH_ALL_TAC
                THEN RW_TAC arith_ss []
                THEN `v = h - (l+1)` by FULL_SIMP_TAC arith_ss []
                THEN PAT_ASSUM ``!h l. X => Y`` (fn th => IMP_RES_TAC (SPECL [``h:num``, ``(l+1):num``] th))
                THEN PAT_ASSUM ``!l h. Z (x)`` (fn th => ASSUME_TAC (SPECL [``(l+1):num``, ``h:num``] th))
                THEN REPEAT STRIP_TAC
                THEN UNDISCH_ALL_TAC
                THEN SEQT_PRESERVE_BEGIN_ABS_TAC ("f l",``l:num``)
                THEN Cases_on `forT (l + 1) h f b`
                THEN Cases_on `forT (l + 1) h f b'`
                THEN FULL_SIMP_TAC (srw_ss()) [] 
                THEN PAT_ASSUM ``∀g s1 s2. mmu_requirements s1 g ⇒
                                           mmu_requirements s2 g ⇒
                                           similar s1 s2 ⇒
                                   (∃a s1' s2'.
                                       (forT (l + 1) h f s1 = ValueState a s1') ∧
                                       (forT (l + 1) h f s2 = ValueState a s2') ∧ similar s1' s2') ∨
                                    ∃e.
                                       (forT (l + 1) h f s1 = Error e) ∧
                                       (forT (l + 1) h f s2 = Error e)``
                     (fn th => ASSUME_TAC (SPECL [``g:word32``, ``b:arm_state``, ``b':arm_state``] th))
                THEN RES_TAC
                THEN FULL_SIMP_TAC (srw_ss()) []
                THEN REPEAT IF_CASES_TAC THEN RW_TAC (srw_ss()) []
                THEN (`access_violation b'' = access_violation b'''` by METIS_TAC [similar_def])
                THEN FULL_SIMP_TAC (srw_ss()) []]);

(* =============   Primitive Actions   ==========================*)
val equal_mem_lem = store_thm(
    "equal_mem_lem",
    `` !s1 s2 g (add:bool[32]) is_write.
       (similar s1 s2)         ==>
       (mmu_requirements s1 g) ==>
       (mmu_requirements s2 g) 
    ==>
       ((s1.memory add) = (s2.memory add))
     \/
       (
        ~ permitted_byte_pure add is_write s1.coprocessors.state.cp15.C1
                                           s1.coprocessors.state.cp15.C2
                                           s1.coprocessors.state.cp15.C3
                                           F s1.memory
        /\
        ~ permitted_byte_pure add is_write s2.coprocessors.state.cp15.C1
                                           s2.coprocessors.state.cp15.C2
                                           s2.coprocessors.state.cp15.C3
                                           F s2.memory
       )``,
   REPEAT STRIP_TAC
       THEN `mmu_requirements_pure s1 g` by FULL_SIMP_TAC (srw_ss()) [mmu_requirements_simp]
       THEN `mmu_requirements_pure s2 g` by FULL_SIMP_TAC (srw_ss()) [mmu_requirements_simp]
       THEN MP_TAC (SPEC ``add:bool[32]`` (blastLib.BBLAST_PROVE ``!add:bool[32]. (¬(add ≤ 0x2FFFFFw ∧ add ≥ 0x100000w)) = (add > 0x2FFFFFw ∨ add < 0x100000w)``))
       THEN MP_TAC (SPEC ``add:word32`` (blastLib.BBLAST_PROVE ``!add:word32. add ≤ 0x1FFFFFw \/ add ≥ 0x200000w``))
       THEN FULL_SIMP_TAC (srw_ss()) [mmu_requirements_pure_def, similar_def]
       THEN METIS_TAC []);


val stay_similar_lem = store_thm(
    "stay_similar_lem",
    ``!s1 s2 g add x. 
      (mmu_requirements s1 g) ==>
      (mmu_requirements s2 g) ==> 
      (similar s1 s2) 
     ==> ((similar (s1 with accesses updated_by CONS (MEM_READ add)) (s2 with accesses updated_by CONS (MEM_READ add)))
     /\  (similar (s1 with accesses updated_by CONS (MEM_WRITE add x)) (s2 with accesses updated_by CONS (MEM_WRITE add x))))``,
     NTAC 8 STRIP_TAC
        THEN FULL_SIMP_TAC (srw_ss()) [similar_def, user_regs_from_state_def, LET_DEF, user_regs_from_list_def, read__reg_def, readT_def]
        THEN MP_TAC (SPECL [``add:word32``, ``x:word8``]  mmu_requirement_accesses_update_lem)
        THEN STRIP_TAC
        THEN RES_TAC
        THEN MP_TAC access_violation_req
        THEN STRIP_TAC
        THEN RES_TAC
        THEN FULL_SIMP_TAC (srw_ss()) [access_violation_pure_def]
        THEN PURE_ONCE_REWRITE_TAC [check_accesses_pure_def]
        THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
        THEN `mmu_requirements_pure s1 g` by FULL_SIMP_TAC (srw_ss()) [mmu_requirements_simp]
        THEN `mmu_requirements_pure s2 g` by FULL_SIMP_TAC (srw_ss()) [mmu_requirements_simp]
        THEN MP_TAC same_setup_same_rights_lem 
        THEN STRIP_TAC 
        THEN RES_TAC
        THEN FULL_SIMP_TAC (srw_ss()) [equal_user_register_def]
        THEN METIS_TAC []);




(* ======= read_mem1 ======== *)
(*  [ find a step-by-step
      version of the proof
      in long_proofs.sml  ]   *)


val read_mem1_thm = store_thm (
    "read_mem1_thm",
    ``!ii add. preserve_relation_mmu (read_mem1 ii add)``,
    PURE_ONCE_REWRITE_TAC [preserve_relation_mmu_def]
       THEN NTAC 8 STRIP_TAC
       THEN Cases_on `read_mem1 ii add s1`
       THEN Cases_on `read_mem1 ii add s2`
       THEN FULL_SIMP_TAC (srw_ss()) []
       THENL [FULL_SIMP_TAC (srw_ss()) [read_mem1_def, writeT_def, readT_def,  seqT_def]
                 THEN (`b = (s1 with accesses updated_by CONS (MEM_READ add))` by 
                            (Cases_on `access_violation (s1 with accesses updated_by CONS (MEM_READ add))`
                               THEN FULL_SIMP_TAC (srw_ss()) []))
                 THEN (`b' = (s2 with accesses updated_by CONS (MEM_READ add))` by 
                            (Cases_on `access_violation (s2 with accesses updated_by CONS (MEM_READ add))`
                               THEN FULL_SIMP_TAC (srw_ss()) []))
                 THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``s2:arm_state``, ``g:word32``, ``add:word32``, ``F``] equal_mem_lem)
                 THEN RES_TAC
                 THENL [`similar b b'  = similar s1 s2` by METIS_TAC [stay_similar_lem]
                           THEN Cases_on `access_violation (s2 with accesses updated_by CONS (MEM_READ add))` 
                           THEN Cases_on `access_violation (s1 with accesses updated_by CONS (MEM_READ add))` 
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN RES_TAC 
                           THEN FULL_SIMP_TAC (srw_ss()) [similar_def,arm_stepTheory.ARM_MODE_def, arm_stepTheory.ARM_READ_CPSR_def]
                           THEN METIS_TAC [],
                        ASSUME_TAC (SPECL [``add:word32``, ``x:word8``, ``s1:arm_state``, ``g:word32``] mmu_requirement_accesses_update_lem)
                           THEN ASSUME_TAC (SPECL [``add:word32``, ``x:word8``, ``s2:arm_state``, ``g:word32``] mmu_requirement_accesses_update_lem)
                           THEN ASSUME_TAC access_violation_req
                           THEN RES_TAC
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN MP_TAC  malicious_read
                           THEN STRIP_TAC
                           THEN RES_TAC
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN METIS_TAC [stay_similar_lem]],
              FULL_SIMP_TAC (srw_ss()) [read_mem1_def, similar_def, seqT_def, writeT_def, readT_def]
                 THEN Cases_on `access_violation (s2 with accesses updated_by CONS (MEM_READ add))` 
                 THEN FULL_SIMP_TAC (srw_ss()) [],
              FULL_SIMP_TAC (srw_ss()) [read_mem1_def, similar_def, seqT_def, writeT_def, readT_def]
                 THEN Cases_on `access_violation (s1 with accesses updated_by CONS (MEM_READ add))` 
                 THEN FULL_SIMP_TAC (srw_ss()) [],
              FULL_SIMP_TAC (srw_ss()) [read_mem1_def, similar_def, seqT_def, writeT_def, readT_def]
                 THEN Cases_on `access_violation (s1 with accesses updated_by CONS (MEM_READ add))` 
                 THEN FULL_SIMP_TAC (srw_ss()) []]);




val read_mem1_ut_thm = store_thm (
    "read_mem1_ut_thm",
    ``!ii add. untouching (read_mem1 ii add)``,
    RW_TAC (srw_ss()) [untouching_def, read_mem1_def, seqT_def, writeT_def, readT_def]
       THEN Cases_on `access_violation (s with accesses updated_by CONS (MEM_READ add))`
       THEN FULL_SIMP_TAC (srw_ss()) [untouched_def]
       THEN RW_TAC (srw_ss()) []);


val write_mem1_ut_thm = store_thm (
    "write_mem1_ut_thm",
    ``!ii add data. untouching (write_mem1 ii add data)``,
    RW_TAC (srw_ss()) [untouching_def, write_mem1_def, seqT_def, writeT_def, readT_def]
       THEN IMP_RES_TAC mmu_requirements_simp
       THEN FULL_SIMP_TAC (srw_ss()) [mmu_requirements_pure_def]
       THEN PAT_ASSUM ``!(add:word32) (is_write:bool). X`` (fn th => ASSUME_TAC (SPECL [``add:word32``, ``T:bool``] th))
       THEN ASSUME_TAC (SPEC ``add:word32`` address_complete)
       THEN Cases_on `gst=guest1`
       THEN Cases_on `gst=guest2`
       THEN (`guest1 <> guest2` by EVAL_TAC)
       THEN FULL_SIMP_TAC (srw_ss()) [] 
       THEN FIRST_PROVE
            [ASSUME_TAC (SPECL [``s:arm_state``, ``s with accesses updated_by CONS (MEM_WRITE add data)``] trivially_untouched_mmu_setup_lem)
                THEN  FULL_SIMP_TAC (srw_ss()) []
                THEN ASSUME_TAC access_violation_req
                THEN RES_TAC
                THEN FULL_SIMP_TAC (srw_ss()) []
                THEN ASSUME_TAC  (SPECL [``s:arm_state``, ``s with accesses updated_by CONS (MEM_WRITE add data)``, ``add:word32``, ``data:word8``] malicious_write)
                THEN FULL_SIMP_TAC (srw_ss()) [untouched_def]
                THEN RW_TAC (srw_ss()) [],
             UNDISCH_ALL_TAC
                THEN CASE_TAC
                THEN RW_TAC (srw_ss()) [untouched_def]
                THEN (RW_TAC (srw_ss()) []
                      THEN EVAL_TAC 
                      THEN RW_TAC (srw_ss()) [inequal_by_inequalities])]);



val write_mem1_thm = store_thm (
    "write_mem1_thm",
    ``!ii add data. preserve_relation_mmu (write_mem1 ii add data)``,
    REPEAT STRIP_TAC
       THEN ASSUME_TAC (SPECL [``ii:iiid``, ``add:word32``, ``data:word8``] write_mem1_untouching_lem)
       THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def, untouching_def]
       THEN REPEAT STRIP_TAC
       THEN RES_TAC
       THEN FULL_SIMP_TAC (srw_ss())  [write_mem1_def, seqT_def, readT_def]
       THEN (REPEAT CASE_TAC) THEN FULL_SIMP_TAC (srw_ss()) [writeT_def] THEN IMP_RES_TAC stay_similar_lem
       THEN PAT_ASSUM ``!(x:word8) (add:word32). X`` (fn th => (ASSUME_TAC (SPECL [``data:word8``, ``add:word32``] th)))
       THEN RW_TAC (srw_ss()) []
       THEN THROW_AWAY_TAC ``similar a b ==> X``
       THEN FULL_SIMP_TAC (srw_ss()) [similar_def, equal_user_register_def]
       THEN STRIP_TAC
       THEN (REPEAT STRIP_TAC)
       THEN UNDISCH_MATCH_TAC ``!(add:word32). X``
       THEN REPEAT (PAT_ASSUM ``!(ii:iiid). X`` (fn th => (MP_TAC (SPEC ``ii:iiid`` th))))
       THEN EVAL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN IMP_RES_TAC untouched_mmu_setup_lem
       THEN IMP_RES_TAC mmu_requirement_accesses_update_lem
       THEN REPEAT (PAT_ASSUM ``!(x:word8) (add:word32). X`` (fn th => (ASSUME_TAC (SPECL [``data:word8``, ``add:word32``] th))))
       THEN ASSUME_TAC (SPECL [``(s1:arm_state) with accesses updated_by CONS (MEM_WRITE (add:word32) (data:word8))``,
                   ``s1 with  <|memory updated_by (add =+ data); accesses updated_by CONS (MEM_WRITE add data)|>``,
                   ``g:word32``] same_setup_same_av_lem)
       THEN ASSUME_TAC (SPECL [``(s2:arm_state) with accesses updated_by CONS (MEM_WRITE (add:word32) (data:word8))``,
                   ``s2 with  <|memory updated_by (add =+ data); accesses updated_by CONS (MEM_WRITE add data)|>``,
                   ``g:word32``] same_setup_same_av_lem)
       THEN FULL_SIMP_TAC (srw_ss()) []);

(* read_mem *)

val read_mem_untouching_lem = store_thm(
    "read_mem_untouching_lem",
    ``!ii desc size. untouching(read_mem ii (desc,size))``,
    RW_TAC (srw_ss()) [read_mem_def, errorT_def, LET_DEF]
       THENL [RW_TAC (srw_ss()) [untouching_def],
              `!x. untouching ((λi. read_mem1 ii ((desc.paddress) + (n2w i))) x)` by METIS_TAC [read_mem1_untouching_lem]
                 THEN IMP_RES_TAC forT_untouching_thm
                 THEN FULL_SIMP_TAC (srw_ss()) []]);



val read_mem_preserving_lem = store_thm(
    "read_mem_preserving_lem",
    ``!ii desc size. preserve_relation_mmu(read_mem ii (desc,size))``,
    RW_TAC (srw_ss()) [read_mem_def, errorT_def, LET_DEF]
       THENL [RW_TAC (srw_ss()) [preserve_relation_mmu_def],
              `!x. untouching ((λi. read_mem1 ii ((desc.paddress) + (n2w i))) x)` by METIS_TAC [read_mem1_untouching_lem]
                 THEN `!x. preserve_relation_mmu ((λi. read_mem1 ii ((desc.paddress) + (n2w i))) x)` by METIS_TAC [read_mem1_preserve_lem]
                 THEN IMP_RES_TAC forT_preserving_thm
                 THEN FULL_SIMP_TAC (srw_ss()) []]);


(* write_mem *)

val write_mem_untouching_lem = store_thm(
    "write_mem_untouching_lem",
    ``!ii desc size value. untouching(write_mem ii (desc,size) value)``,
    RW_TAC (srw_ss()) [write_mem_def, errorT_def, LET_DEF]
       THENL [RW_TAC (srw_ss()) [untouching_def],
              RW_TAC (srw_ss()) [untouching_def],
              `!x. untouching ((λi. write_mem1 ii ((desc.paddress) + (n2w i)) (EL i value))  x)` by METIS_TAC [write_mem1_untouching_lem]
                 THEN IMP_RES_TAC forT_untouching_thm 
                 THEN ASSUME_TAC constT_untouching_unit_lem
                 THEN SEQT_UNTOUCHED_TAC]);



val write_mem_preserving_lem = store_thm(
    "write_mem_preserving_lem",
    ``!ii desc size value. preserve_relation_mmu(write_mem ii (desc,size) value)``,
    RW_TAC (srw_ss()) [write_mem_def, errorT_def, LET_DEF]
       THENL [RW_TAC (srw_ss()) [preserve_relation_mmu_def],
              RW_TAC (srw_ss()) [preserve_relation_mmu_def],
              `!x. untouching ((λi. write_mem1 ii ((desc.paddress) + (n2w i)) (EL i value)) x)` by METIS_TAC [write_mem1_untouching_lem]
                 THEN (`!x. preserve_relation_mmu ((λi. write_mem1 ii ((desc.paddress) + (n2w i)) (EL i value)) x)` by METIS_TAC [write_mem1_preserve_lem])
                 THEN IMP_RES_TAC forT_preserving_thm
                 THEN IMP_RES_TAC forT_untouching_thm
                 THEN ASSUME_TAC constT_preserving_unit_lem
                 THEN (REPEAT (PAT_ASSUM ``!l h. X`` (fn th => ASSUME_TAC (SPECL [``0``, ``LENGTH (value:word8 list) - 1``] th))))
                 THEN (REPEAT (PAT_ASSUM ``!x. X`` (fn th => IMP_RES_TAC th)))
                 THEN (REPEAT (PAT_ASSUM ``~X`` (fn th => IMP_RES_TAC th)))
                 THEN IMP_RES_TAC seqT_preserving_thm]);





val psrs_update_thm = store_thm ("psrs_update_thm ",
				 ``! t s Y. (t = (s with psrs updated_by Y)) 
				==> (s.accesses = t.accesses) /\ (s.memory = t.memory) 
		      /\ (s.coprocessors = t.coprocessors)``
			       ,RW_TAC (srw_ss()) []);
val write__psr_thm = 
    store_thm ("write__psr_thm",
	       ``! psr cp. preserve_relation_mmu (write__psr ii psr cp)``,
	       RW_TAC (srw_ss()) [preserve_relation_mmu_def,write__psr_def,writeT_def,similar_def]
		      THEN EVAL_TAC
		      THEN RW_TAC (srw_ss()) []
		      THEN UNDISCH_TAC ``equal_user_register s1 s2``
		      THEN EVAL_TAC
		      THEN RW_TAC (srw_ss()) []
		      THEN REPEAT (PAT_ASSUM ``!ii:(iiid). stm`` 
					     (fn thm => ASSUME_TAC (SPEC ``ii':iiid`` thm)))
		      THEN ASSUME_TAC	 psrs_update_thm
		      THEN ASSUME_TAC (SPECL [``s2:arm_state``, 
					      ``s2 with psrs updated_by ((ii.proc,psr) =+ cp:(ARMpsr))``, ``g:bool[32]``] 
					     trivially_untouched_av_lem)
		      THEN ASSUME_TAC (SPECL [``s1:arm_state``,
					      ``s1 with psrs updated_by ((ii.proc,psr) =+ cp:(ARMpsr))``, ``g:bool[32]``]	 
					     (trivially_untouched_av_lem))
		      THEN RES_TAC
		      THEN FULL_SIMP_TAC (srw_ss()) []);


val write__psr_ut_thm = 
    store_thm ("write__psr_ut_thm",
	       ``untouching (write__psr ii CPSR cp)``,
	       RW_TAC (srw_ss()) [untouched_def,untouching_def,write__psr_def, writeT_def]
		      THEN (UNDISCH_TAC ``psr ≠ CPSR``)
		      THEN EVAL_TAC
		      THEN  RW_TAC (srw_ss()) []);

 g `untouching (write__psr ii SPSR_und cp)`;





val errorT_thm = store_thm("errorT_thm",
``! s. preserve_relation_mmu (errorT s)``,
(RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def,errorT_def]));

val errorT_ut_thm = store_thm("errorT_ut_thm",
``! s. untouching (errorT s)``,
(RW_TAC (srw_ss()) [untouching_def,untouched_def,errorT_def]));

val arch_version_thm = store_thm("arch_version_thm",
  `` preserve_relation_mmu (arch_version ii) ``,
 RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def,arch_version_def,readT_def,read_arch_def,seqT_def,readT_def]
	THEN computeLib.RESTR_EVAL_TAC [``equal_user_register``]
	THEN  RW_TAC (srw_ss())[]);

val arch_version_ut_thm = store_thm("arch_version_ut_thm",
  `` untouching (arch_version ii) ``,
 RW_TAC (srw_ss()) [untouching_def]
THEN FULL_SIMP_TAC (srw_ss()) [untouched_def,arch_version_def,readT_def,read_arch_def,seqT_def,readT_def]
	THEN Cases_on `access_violation s`
	THEN FULL_SIMP_TAC (srw_ss()) []
	THEN UNDISCH_TAC ``return (version_number s.information.arch) s = ValueState a s'``
	THEN computeLib.RESTR_EVAL_TAC [``equal_user_register``]
	THEN FULL_SIMP_TAC (srw_ss()) []);

g ` untouching (arch_version ii) `;

val read_cpsr_ut_thm = store_thm (
    "read_cpsr_ut_thm",
    ``untouching (read_cpsr ii)``,
    RW_TAC (srw_ss()) [untouching_def]
       THEN FULL_SIMP_TAC (srw_ss()) [untouched_def, read_cpsr_def, read__psr_def, readT_def]);



val read_cpsr_thm = store_thm("read_cpsr_thm",
  `` preserve_relation_mmu (read_cpsr ii) ``,
 (RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def,
							    read_cpsr_def,read__psr_def,readT_def]));

val read_cpsr_ut_thm = store_thm (
    "read_cpsr_ut_thm",
    ``untouching (read_cpsr ii) (assert_mode 16w)``,
    RW_TAC (srw_ss()) [untouching_def]
       THEN FULL_SIMP_TAC (srw_ss()) [untouched_def, read_cpsr_def, read__psr_def, readT_def,assert_mode_def,read_mode_def]);


val read_scr_thm = store_thm("read_scr_thm",
  ``! ii.  preserve_relation_mmu (read_scr ii) ``,
 (RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def,read_scr_def,readT_def]));

val read_scr_ut_thm = store_thm (
    "read_scr_ut_thm",
    ``!ii. untouching (read_scr ii)``,
    RW_TAC (srw_ss()) [untouching_def]
       THEN FULL_SIMP_TAC (srw_ss()) [untouched_def,read_scr_def, readT_def]);




val read_pc_thm = store_thm("read_pc_thm",
  ``! ii .  preserve_relation_mmu (read_pc ii) ``,
 (RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def,read_pc_def,equal_user_register_def,read__reg_def,readT_def]));

val read_pc_ut_thm = store_thm (
    "read_pc_ut_thm",
    ``!ii. untouching (read_pc ii)``,
    RW_TAC (srw_ss()) [untouching_def]
       THEN FULL_SIMP_TAC (srw_ss()) [untouched_def,read_pc_def,read__reg_def,readT_def,equal_user_register_def]);


val untouched_av_on_coprocessor_update_lem = store_thm(
     "untouched_av_on_coprocessor_update_lem",
     ``!s gst. (mmu_requirements s gst) ==>
       (access_violation s =
        access_violation ((arm_state_coprocessors_fupd 
(Coprocessors_state_fupd (coproc_state_cp15_fupd (\cp15. cp15 with <| 
SCR := scr |>)))) s))``,
     (NTAC 2 STRIP_TAC)
        THEN (`mmu_requirements ( (arm_state_coprocessors_fupd 
(Coprocessors_state_fupd (coproc_state_cp15_fupd (\cp15. cp15 with <| 
SCR := scr |>)))) s) gst = mmu_requirements s gst` by RW_TAC 
(srw_ss()) [mmu_requirements_def])
        THEN REPEAT STRIP_TAC
        THEN RES_TAC
        THEN IMP_RES_TAC access_violation_req
        THEN RW_TAC (srw_ss()) [access_violation_pure_def]);


val write_scr_thm = store_thm("write_scr_thm",
  ``! ii .  preserve_relation_mmu (write_scr ii scr) ``,
 (RW_TAC (srw_ss()) [preserve_relation_mmu_def,similar_def,write_scr_def,writeT_def])
THENL [UNDISCH_TAC ``equal_user_register s1 s2``
THEN EVAL_TAC
THEN RW_TAC (srw_ss()) [], ASSUME_TAC (SPECL [``s1:arm_state``,``g:word32``] untouched_av_on_coprocessor_update_lem)
THEN RES_TAC
THEN ASSUME_TAC (SPECL [``s2:arm_state``,``g:word32``] untouched_av_on_coprocessor_update_lem)
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) []]
);

val write_scr_ut_thm = 
    store_thm ("write_scr_ut_thm",
	       ``untouching (write_scr ii scr)``,
	       RW_TAC (srw_ss()) [untouched_def,untouching_def,write_scr_def, writeT_def]);
