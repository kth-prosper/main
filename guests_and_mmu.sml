(* ============ LOADING =========== *)
;
(*
loadPath := "/NOBACKUP/workspaces/oschwarz/hol4.k.7/examples/ARM/v7/" :: !loadPath;

load "/NOBACKUP/workspaces/nargeskh/hol4.k.7/examples/ARM/v7/relationTheory";
open relationTheory;
open armLib;
open HolKernel Parse boolLib bossLib;

(* now load 
     /NOBACKUP/workspaces/nargeskh/hol4.k.7/examples/ARM/v7/holmodel/machine-obs-Oct8.sml 
     /NOBACKUP/workspaces/nargeskh/hol4.k.7/examples/ARM/v7/holmodel/relation_lemmas.sml
without the loading parts there *)

use "/opt/localworkspace/oschwarz/hol/mmu5.sml"; *)
load "Cond_rewrite";
load "blastLib";     

(* === MMU requirements  === *)



(* what we assume when guests are running *)
val mmu_requirements_def = Define `mmu_requirements state id = 
!add is_write u p m.
  ((u,p,m) = permitted_byte add 
                            is_write
                            state.coprocessors.state.cp15.C1 
                            state.coprocessors.state.cp15.C2 
                            state.coprocessors.state.cp15.C3
                            F
                            state.memory)
==>
    u
/\  ( ((add <=+ guest1_max_adr) /\ (add >=+  guest1_min_adr))   ==>    (p = (id=guest1)) )
/\  ( ((add <=+ guest2_max_adr) /\ (add >=+  guest2_min_adr))   ==>    (p = (id=guest2)) )
/\  ( ((add >+  guest2_max_adr) \/ (add <+   guest1_min_adr))   ==>    (~p) )
/\  ((state.coprocessors.state.cp15.C2  && (0xFFFFC000w:bool[32])) >=+  0w)
/\  ((state.coprocessors.state.cp15.C2  && (0xFFFFC000w:bool[32])) <+  guest1_min_adr)
/\  (((state.coprocessors.state.cp15.C2  && (0xFFFFC000w:bool[32])) + 4w * 4095w + 3w) <+   guest1_min_adr)`;





(* some consequences from the above for permitted_byte_pure *)
val mmu_requirements_pure_def = Define `mmu_requirements_pure state id =
!add is_write.
( ((add <=+ guest1_max_adr) /\ (add >=+ guest1_min_adr))   ==>
  ((id=guest1) = permitted_byte_pure add 
                                is_write
                                state.coprocessors.state.cp15.C1 
                                state.coprocessors.state.cp15.C2 
                                state.coprocessors.state.cp15.C3
                                F
                                state.memory))  /\
( ((add <=+ guest2_max_adr ) /\ (add >=+ guest2_min_adr))   ==>
  ((id=guest2) = permitted_byte_pure add 
                                is_write
                                state.coprocessors.state.cp15.C1 
                                state.coprocessors.state.cp15.C2 
                                state.coprocessors.state.cp15.C3
                                F
                                state.memory))  /\
( ((add >+ guest2_max_adr ) \/ (add <+  guest1_min_adr))   ==>
  (~ permitted_byte_pure add 
                                is_write
                                state.coprocessors.state.cp15.C1 
                                state.coprocessors.state.cp15.C2 
                                state.coprocessors.state.cp15.C3
                                F
                                state.memory))`;


(* lemma: mmu_requirements_pure follows from mmu_requirements *)
val mmu_requirements_simp = store_thm(
    "mmu_requirements_simp",
    ``!s g. mmu_requirements s g ==> mmu_requirements_pure s g``,
    PURE_ONCE_REWRITE_TAC [mmu_requirements_pure_def]
      THEN NTAC 5 STRIP_TAC
      THEN Cases_on `permitted_byte add is_write s.coprocessors.state.cp15.C1 s.coprocessors.state.cp15.C2 s.coprocessors.state.cp15.C3 F s.memory` 
      THEN pairLib.PairCases_on `r`
      THEN NTAC 2 STRIP_TAC
      THEN TRY DISCH_TAC
      THENL[`q /\ (r0 = (g=guest1))` by METIS_TAC [mmu_requirements_def]
              THEN METIS_TAC [permitted_byte_simp],
           `q /\ (r0 = (g=guest2))` by METIS_TAC [mmu_requirements_def]
              THEN METIS_TAC [permitted_byte_simp],
           `q /\ ~r0` by METIS_TAC [mmu_requirements_def]
              THEN METIS_TAC [permitted_byte_simp]
           ]
);


(* lemma: mmu_requirements don't change by access list update *)

val mmu_requirement_accesses_update_lem = store_thm(
    "mmu_requirement_accesses_update_lem",
    ``!add x s g. 
      ((mmu_requirements s g) = (mmu_requirements (s with accesses updated_by CONS (MEM_READ add)) g))
   /\ ((mmu_requirements s g) = (mmu_requirements (s with accesses updated_by CONS (MEM_WRITE add x)) g))``,
    FULL_SIMP_TAC (srw_ss()) [mmu_requirements_def]);

val mmu_requirement_accesses_update_lem2 = store_thm(
    "mmu_requirement_accesses_update_lem2",
    ``!add x s g. 
      ((mmu_requirements s g) = (mmu_requirements (s with accesses updated_by CONS (MEM_READ add) o other) g))
   /\ ((mmu_requirements s g) = (mmu_requirements (s with accesses updated_by CONS (MEM_WRITE add x) o other) g))``,
    FULL_SIMP_TAC (srw_ss()) [mmu_requirements_def]);



(* lemma: same setup -->  same access rights *)

val same_setup_same_rights_lem = store_thm(
    "same_setup_same_rights_lem", 
    ``! s1 s2 g add is_write.
      mmu_requirements_pure s1 g ==>
      mmu_requirements_pure s2 g
    ==>
      (permitted_byte_pure add is_write s1.coprocessors.state.cp15.C1
                                        s1.coprocessors.state.cp15.C2
                                        s1.coprocessors.state.cp15.C3
                                        F s1.memory
      = permitted_byte_pure add is_write s2.coprocessors.state.cp15.C1
                                         s2.coprocessors.state.cp15.C2
                                         s2.coprocessors.state.cp15.C3
                                         F s2.memory)``,
    REPEAT STRIP_TAC
       THEN MP_TAC (SPEC ``add:word32`` negated_and_or)
       THEN MP_TAC (SPEC ``add:word32`` address_border)
       THEN FULL_SIMP_TAC (srw_ss()) [mmu_requirements_pure_def]
       THEN METIS_TAC []);


val same_setup_same_check_accesses_lem = store_thm(
    "same_setup_same_check_accesses_lem", 
    ``! s1 s2 g accesses.
      mmu_requirements_pure s1 g ==>
      mmu_requirements_pure s2 g
    ==>
      (check_accesses_pure accesses s1.coprocessors.state.cp15.C1
                                    s1.coprocessors.state.cp15.C2
                                    s1.coprocessors.state.cp15.C3 F s1.memory
      =check_accesses_pure accesses s2.coprocessors.state.cp15.C1
                                    s2.coprocessors.state.cp15.C2
                                    s2.coprocessors.state.cp15.C3 F s2.memory)``,
    REPEAT STRIP_TAC
       THEN Induct_on `accesses` 
       THEN PURE_ONCE_REWRITE_TAC [check_accesses_pure_def]
       THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
       THEN STRIP_TAC
       THEN CASE_TAC
       THEN ASSUME_TAC (SPECL [``s1:arm_state``, ``s2:arm_state``, ``g:word32``, ``c:word32``] same_setup_same_rights_lem)
       THEN FULL_SIMP_TAC (srw_ss()) []);


val same_setup_same_av_pure_lem = store_thm(
    "same_setup_same_av_pure_lem",
    ``! s1 s2 g.
      mmu_requirements_pure s1 g ==>
      mmu_requirements_pure s2 g ==>
      (s1.accesses = s2.accesses)
    ==>
      (access_violation_pure s1 = access_violation_pure s2)``,
    REPEAT STRIP_TAC
       THEN RW_TAC (srw_ss()) [access_violation_pure_def]
       THEN METIS_TAC [same_setup_same_check_accesses_lem]);



(* === well-defined MMU setup allows (simpler) computation of access violation === *)

val access_violation_req = store_thm (
    "access_violation_req",
    ``!s id. (mmu_requirements s id) 
      ==> (access_violation s = access_violation_pure s)``,
    REPEAT STRIP_TAC
      THEN Cond_rewrite.COND_REWRITE1_TAC (SPEC ``s:arm_state`` access_violation_simp_FST)      
      THEN FULL_SIMP_TAC (srw_ss()) [access_violation_full_def]
      THEN  `!add is_write. 
            ((u,p,m) = (permitted_byte add is_write s.coprocessors.state.cp15.C1 s.coprocessors.state.cp15.C2 s.coprocessors.state.cp15.C3 F s.memory))
            ==> u` by METIS_TAC [mmu_requirements_def]
     THEN  `!add is_write. 
            FST (permitted_byte add is_write s.coprocessors.state.cp15.C1 s.coprocessors.state.cp15.C2 s.coprocessors.state.cp15.C3 F s.memory)` 
            by (RW_TAC (srw_ss()) []
                  THEN Cases_on `permitted_byte add is_write s.coprocessors.state.cp15.C1 s.coprocessors.state.cp15.C2 s.coprocessors.state.cp15.C3 F s.memory`
                  THEN pairLib.PairCases_on `r`
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN METIS_TAC[mmu_requirements_def]
                )
     THEN METIS_TAC [ check_accesses_understand]);




val same_setup_same_av_lem = store_thm(
    "same_setup_same_av_lem",
    ``! s1 s2 g.
      mmu_requirements s1 g ==>
      mmu_requirements s2 g ==>
      (s1.accesses = s2.accesses)
    ==>
      (access_violation s1 = access_violation s2)``,
    REPEAT STRIP_TAC
       THEN IMP_RES_TAC access_violation_req
       THEN IMP_RES_TAC mmu_requirements_simp
       THEN ASSUME_TAC same_setup_same_av_pure_lem
       THEN METIS_TAC []);





(* malicious_read and malicious_write  *)

val malicious_read = store_thm (
    "malicious_read",
    ``!s t address. (t = s with accesses updated_by CONS (MEM_READ address)) ==>
                 (~ permitted_byte_pure address F s.coprocessors.state.cp15.C1 s.coprocessors.state.cp15.C2 s.coprocessors.state.cp15.C3 F s.memory  \/
                  ~ permitted_byte_pure address F t.coprocessors.state.cp15.C1 t.coprocessors.state.cp15.C2 t.coprocessors.state.cp15.C3 F t.memory)
            ==>   access_violation_pure t``,
    REPEAT STRIP_TAC
      THEN `?restlist. t.accesses = (MEM_READ address)::restlist` by (EXISTS_TAC ``s.accesses`` THEN FULL_SIMP_TAC (srw_ss()) [])
      THEN `t.memory = s.memory` by FULL_SIMP_TAC (srw_ss()) []
      THEN `t.coprocessors = s.coprocessors` by FULL_SIMP_TAC (srw_ss()) []
      THEN PURE_ONCE_REWRITE_TAC [access_violation_pure_def]
      THEN PURE_ONCE_REWRITE_TAC [check_accesses_pure_def]
      THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
);


val malicious_read2 = store_thm (
    "malicious_read2",
    ``!s t address. (t = s with accesses updated_by CONS (MEM_READ address) o other) ==>
                 (~ permitted_byte_pure address F s.coprocessors.state.cp15.C1 s.coprocessors.state.cp15.C2 s.coprocessors.state.cp15.C3 F s.memory  \/
                  ~ permitted_byte_pure address F t.coprocessors.state.cp15.C1 t.coprocessors.state.cp15.C2 t.coprocessors.state.cp15.C3 F t.memory)
            ==>   access_violation_pure t``,
    REPEAT STRIP_TAC
      THEN `?restlist. t.accesses = (MEM_READ address)::restlist` by (EXISTS_TAC ``(other (s.accesses)):(memory_access list)`` THEN FULL_SIMP_TAC (srw_ss()) [])
      THEN `t.memory = s.memory` by FULL_SIMP_TAC (srw_ss()) []
      THEN `t.coprocessors = s.coprocessors` by FULL_SIMP_TAC (srw_ss()) []
      THEN PURE_ONCE_REWRITE_TAC [access_violation_pure_def]
      THEN PURE_ONCE_REWRITE_TAC [check_accesses_pure_def]
      THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]);


val malicious_write = store_thm (
    "malicious_write",
    ``!s t address value. (t = s with accesses updated_by CONS (MEM_WRITE address value)) ==>
                 (~ permitted_byte_pure address T s.coprocessors.state.cp15.C1 s.coprocessors.state.cp15.C2 s.coprocessors.state.cp15.C3 F s.memory  \/
                  ~ permitted_byte_pure address T t.coprocessors.state.cp15.C1 t.coprocessors.state.cp15.C2 t.coprocessors.state.cp15.C3 F t.memory)
            ==>   access_violation_pure t``,
    REPEAT STRIP_TAC
      THEN `?restlist. t.accesses = (MEM_WRITE address value)::restlist` by (EXISTS_TAC ``s.accesses`` THEN FULL_SIMP_TAC (srw_ss()) [])
      THEN `t.memory = s.memory` by FULL_SIMP_TAC (srw_ss()) []
      THEN `t.coprocessors = s.coprocessors` by FULL_SIMP_TAC (srw_ss()) []
      THEN PURE_ONCE_REWRITE_TAC [access_violation_pure_def]
      THEN PURE_ONCE_REWRITE_TAC [check_accesses_pure_def]
      THEN FULL_SIMP_TAC (srw_ss()) [LET_DEF]
);



(* predicate "word aligned around address add is readable" *)


val aligned_word_readable_def = Define `aligned_word_readable s is_thumb add =
 (  permitted_byte_pure (add) F s.coprocessors.state.cp15.C1 s.coprocessors.state.cp15.C2 s.coprocessors.state.cp15.C3 F s.memory 
       /\ (is_thumb ==> (  permitted_byte_pure (align(add,2)) F s.coprocessors.state.cp15.C1
                                                        s.coprocessors.state.cp15.C2 
        						 s.coprocessors.state.cp15.C3 F s.memory
                               /\ permitted_byte_pure (align (add,2) + 1w) F s.coprocessors.state.cp15.C1
        	                                              s.coprocessors.state.cp15.C2 
        						      s.coprocessors.state.cp15.C3 F s.memory))
        
       /\ (~is_thumb ==> (  permitted_byte_pure (align(add,4)) F s.coprocessors.state.cp15.C1
                                                        s.coprocessors.state.cp15.C2 
        						 s.coprocessors.state.cp15.C3 F s.memory
                               /\ permitted_byte_pure (align (add,4) + 1w) F s.coprocessors.state.cp15.C1
        	                                              s.coprocessors.state.cp15.C2 
        						      s.coprocessors.state.cp15.C3 F s.memory
                               /\ permitted_byte_pure (align (add,4) + 2w) F s.coprocessors.state.cp15.C1
        	                                              s.coprocessors.state.cp15.C2 
        						      s.coprocessors.state.cp15.C3 F s.memory
                               /\ permitted_byte_pure (align (add,4) + 3w) F s.coprocessors.state.cp15.C1
        	                                              s.coprocessors.state.cp15.C2 
        						      s.coprocessors.state.cp15.C3 F s.memory)))`;

