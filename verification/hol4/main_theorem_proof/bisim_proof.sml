(**********************************************************************************)
(*                 proof of bisimlarity due to the user transition                *)
(**********************************************************************************)
fun user_bisim_states_ValueState_tac_list gst = 
    RES_TAC 
	THEN FULL_SIMP_TAC (srw_ss()) [candidate_relation_def,
				       outer_full_relation_user_def]
	THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``,``sr':arm_state``, ``si:composite_arm_state``, 
	``cycle:int``, ``a:unit``,
	``rc:int``,gst] outer_user_mode_thm
	 THEN UNDISCH_ALL_TAC
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN RW_TAC (srw_ss()) [];


val user_bisim_states_ValueState_thm = store_thm("user_bisim_states_ValueState_thm",
  `` ! sr sr' cycle rc ic si si' mode' g a a'.
  (unique_guest g) ==>
  (one_step_real  sr cycle <|proc:=0|> = (ValueState a sr',rc)) ==>
  (one_step_ideal si cycle <|proc:=0|> = (ValueState a' si',ic,mode')) ==>
  (candidate_relation (sr,cycle) (si,cycle) g) ==>
   (ARM_MODE sr' = 16w) ==> 
  candidate_relation (sr',rc) (si',ic) g ``
,
 ASSUME_TAC  bisimilar_correct_usermode_states
        THEN ASSUME_TAC	 bisimilar_mode_assert_thm
        THEN RW_TAC (srw_ss()) [unique_guest_def]
        THENL 
	[ user_bisim_states_ValueState_tac_list ``guest1:bool[32]``,
	 user_bisim_states_ValueState_tac_list ``guest2:bool[32]``]
						);
  




(**********************************************************)
(*            proof of being in the same mode             *)
(**********************************************************)

val user_identical_mode_ValueState_states_thm = store_thm(
  "user_identical_mode_ValueState_user_states_thm",
  `` ! sr sr' cycle rc ic si si'  mode' g a a'.
  (unique_guest g) ==>
  (one_step_real sr cycle <|proc:=0|> = (ValueState a sr',rc)) ==>
  (one_step_ideal si cycle <|proc:=0|> = (ValueState a' si',ic,mode')) ==>
  (candidate_relation (sr,cycle) (si,cycle) g) ==>
   (ARM_MODE sr' = 16w) ==> 
   (mode'=16w) ``,
  RW_TAC (srw_ss()) [unique_guest_def,candidate_relation_def,
		     outer_full_relation_user_def]
     	 THEN  IMP_RES_TAC correct_usermode_states_mode_assert_thm
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN (REPEAT (WEAKEN_TAC is_imp))
	 THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``,``sr':arm_state``, ``si:composite_arm_state``,
	``cycle:int``, ``a:unit``,
	``rc:int``,``guest1``] outer_user_mode_thm
	 THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``,``sr':arm_state``, ``si:composite_arm_state``,
	``cycle:int``, ``a:unit``,
	``rc:int``,``guest2``] outer_user_mode_thm
	 THEN UNDISCH_ALL_TAC
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN RW_TAC (srw_ss()) []
	);



val user_same_elapsed_cycle_ValueState_states_thm = store_thm(
  "user_same_elapsed_cycle_ValueState_user_states_thm",
  `` ! sr sr' cycle rc ic si si'  mode' g a a'.
  (unique_guest g) ==>
  (one_step_real sr cycle <|proc:=0|> = (ValueState a sr',rc)) ==>
  (one_step_ideal si cycle <|proc:=0|> = (ValueState a' si',ic,mode')) ==>
  (candidate_relation (sr,cycle) (si,cycle) g) ==>
  (ic=rc) ``,
  RW_TAC (srw_ss()) [unique_guest_def,candidate_relation_def,
		     outer_full_relation_user_def]
     	 THEN  IMP_RES_TAC correct_usermode_states_mode_assert_thm
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN (REPEAT (WEAKEN_TAC is_imp))
	 THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``,``sr':arm_state``, ``si:composite_arm_state``,
	``cycle:int``, ``a:unit``,
	``rc:int``,``guest1``] outer_user_mode_thm
	 THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``,``sr':arm_state``, ``si:composite_arm_state``,
	``cycle:int``, ``a:unit``,
	``rc:int``,``guest2``] outer_user_mode_thm
	 THEN UNDISCH_ALL_TAC
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN RW_TAC (srw_ss()) []
	);


(*********************************************************************)
(*********************************************************************)
(*        the case that next mode is not user mode (HANDLERS)        *)
(*********************************************************************)
(*********************************************************************)

(* proofManagerLib.r(1); *)

(**********************************************************)
(*           proof of going to the same modes             *)
(**********************************************************)
val switched_identical_mode_ValueState_states_thm = store_thm(
  "switched_identical_mode_ValueState_states_thm",
  `` ! sr sr' cycle rc ic si si' mode' g a a'.
  (unique_guest g) ==>
  (outer_user_mode_constraints sr si g)     	==>
  (kth_hyp_invariants sr)       	       	==>
  (mmu_boot_setup sr)			       	==>
  (mmu_boot_setup si.machine1)	       	==>
  (mmu_boot_setup si.machine2)	       	==>
  (mmu_coprocessor_setup sr g)	       	==>
  (mmu_coprocessor_setup si.machine1 guest1) 	==>
  (mmu_coprocessor_setup si.machine2 guest2) 	==>
  (one_step_real sr cycle <|proc:=0|> = (ValueState a sr',rc)) ==>
  (one_step_ideal si cycle <|proc:=0|> = (ValueState a' si',ic,mode')) ==>
  (correct_user_mode_states sr si g) ==>
  (ARM_MODE sr' <> 16w) ==>
  (ARM_MODE sr' = mode')   ``,
  RW_TAC (srw_ss()) [unique_guest_def]
   	 THEN  IMP_RES_TAC correct_usermode_states_mode_assert_thm
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN (REPEAT (WEAKEN_TAC is_imp))
	 THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``, 
	  ``sr':arm_state``, ``si:composite_arm_state``, ``a:unit``,
	  ``cycle:int``, 
	  ``rc:int``,``guest1``] outer_switched_mode_thm
	 THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``, 
	  ``sr':arm_state``, ``si:composite_arm_state``, ``a:unit``,
	  ``cycle:int``, 
	  ``rc:int``,``guest2``] outer_switched_mode_thm
	 THEN UNDISCH_ALL_TAC
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN RW_TAC (srw_ss()) []

);


val correct_switched_mode_in_switched_mode_thm = store_thm(
  "correct_switched_mode_in_switched_mode_thm",
  `` ! sr sr' cycle rc ic si si' mode' g a a'.
  (unique_guest g) ==>
   (outer_user_mode_constraints sr si g)     	==>
  (kth_hyp_invariants sr)       	       	==>
  (mmu_boot_setup sr)			       	==>
  (mmu_boot_setup si.machine1)	       	==>
  (mmu_boot_setup si.machine2)	       	==>
  (mmu_coprocessor_setup sr g)	       	==>
  (mmu_coprocessor_setup si.machine1 guest1) 	==>
  (mmu_coprocessor_setup si.machine2 guest2) 	==>
  (one_step_real sr cycle <|proc:=0|> = (ValueState a sr',rc)) ==>
  (one_step_ideal si cycle <|proc:=0|> = (ValueState a' si',ic,mode')) ==>
  (correct_user_mode_states sr si g) ==>
  (ARM_MODE sr' <> 16w) ==>
  ((correct_switched_mode_states sr' si' sr si g))   ``,
  RW_TAC (srw_ss()) [unique_guest_def, candidate_relation_def]
     	 THEN IMP_RES_TAC correct_usermode_states_mode_assert_thm
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``, ``sr':arm_state``,  ``si:composite_arm_state``, ``a:unit``,
	  ``cycle:int``, 
	  ``rc:int``,``guest1``] outer_switched_mode_thm
	 THEN ASSUME_SPECL_TAC 	
	 [``sr:arm_state``, 
	  ``sr':arm_state``, ``si:composite_arm_state``, ``a:unit``,
	  ``cycle:int``, 
	  ``rc:int``,``guest2``]  outer_switched_mode_thm
	 THEN UNDISCH_ALL_TAC
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN RW_TAC (srw_ss()) []
						 );



val same_elapsed_cycle_in_switched_mode_thm = store_thm(
  "same_elapsed_cycle_in_switched_mode_thm",
  `` ! sr sr' cycle rc ic si si' mode' g a a'.
  (unique_guest g) ==>
  (outer_user_mode_constraints sr si g)     	==>
  (kth_hyp_invariants sr)       	       	==>
  (mmu_boot_setup sr)			       	==>
  (mmu_boot_setup si.machine1)	       	==>
  (mmu_boot_setup si.machine2)	       	==>
  (mmu_coprocessor_setup sr g)	       	==>
  (mmu_coprocessor_setup si.machine1 guest1) 	==>
  (mmu_coprocessor_setup si.machine2 guest2) 	==>
  (one_step_real sr cycle <|proc:=0|> = (ValueState a sr',rc)) ==>
  (one_step_ideal si cycle <|proc:=0|> = (ValueState a' si',ic,mode')) ==>
  (correct_user_mode_states sr si g) ==>
  (ARM_MODE sr' <> 16w) ==>
  (rc=ic)   ``,
  RW_TAC (srw_ss()) [unique_guest_def, candidate_relation_def]
   	 
     	 THEN IMP_RES_TAC correct_usermode_states_mode_assert_thm
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``, ``sr':arm_state``,  ``si:composite_arm_state``, ``a:unit``,
	  ``cycle:int``, 
	  ``rc:int``,``guest1``] outer_switched_mode_thm
	 THEN ASSUME_SPECL_TAC 	
	 [``sr:arm_state``, 
	  ``sr':arm_state``, ``si:composite_arm_state``, ``a:unit``,
	  ``cycle:int``, 
	  ``rc:int``,``guest2``]  outer_switched_mode_thm
	 THEN UNDISCH_ALL_TAC
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN RW_TAC (srw_ss()) []
						 );


val mmu_setup_in_switched_mode_thm = store_thm(
  "mmu_setup_in_switched_mode_thm",
  `` ! sr sr' cycle rc ic si si' mode' g a a'.
  (unique_guest g) ==>
   (outer_user_mode_constraints sr si g)     	==>
  (kth_hyp_invariants sr)       	       	==>
  (mmu_boot_setup sr)			       	==>
  (mmu_boot_setup si.machine1)	       	==>
  (mmu_boot_setup si.machine2)	       	==>
  (mmu_coprocessor_setup sr g)	       	==>
  (mmu_coprocessor_setup si.machine1 guest1) 	==>
  (mmu_coprocessor_setup si.machine2 guest2) 	==>
  (one_step_real sr cycle <|proc:=0|> = (ValueState a sr',rc)) ==>
  (one_step_ideal si cycle <|proc:=0|> = (ValueState a' si',ic,mode')) ==>
  (correct_user_mode_states sr si g) ==>
  (ARM_MODE sr' <> 16w) ==>
  ( (mmu_boot_setup sr')			       	/\
  (mmu_boot_setup si'.machine1)			/\
  (mmu_boot_setup si'.machine2)			/\
  (mmu_coprocessor_setup sr' g)			/\
  (mmu_coprocessor_setup si'.machine1 guest1)	/\
  (mmu_coprocessor_setup si'.machine2 guest2))
    ``,
  RW_TAC (srw_ss()) [unique_guest_def, candidate_relation_def]
   	 
     	 THEN IMP_RES_TAC correct_usermode_states_mode_assert_thm
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``, ``sr':arm_state``,  ``si:composite_arm_state``, ``a:unit``,
	  ``cycle:int``,
	  ``rc:int``,``guest1``] outer_switched_mode_thm
	 THEN ASSUME_SPECL_TAC 	
	 [``sr:arm_state``, 
	  ``sr':arm_state``, ``si:composite_arm_state``,``a:unit``,
	  ``cycle:int``, 
	  ``rc:int``,``guest2``]  outer_switched_mode_thm
	 THEN UNDISCH_ALL_TAC
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN RW_TAC (srw_ss()) []	
 );

val kth_hyp_invars_in_switched_mode_thm = store_thm(
  "kth_hyp_invars_in_switched_mode_thm",
  `` ! sr sr' cycle rc ic si si' mode' g a a'.
  (unique_guest g) ==>
   (outer_user_mode_constraints sr si g)     	==>
  (kth_hyp_invariants sr)       	       	==>
  (mmu_boot_setup sr)			       	==>
  (mmu_boot_setup si.machine1)	       	==>
  (mmu_boot_setup si.machine2)	       	==>
  (mmu_coprocessor_setup sr g)	       	==>
  (mmu_coprocessor_setup si.machine1 guest1) 	==>
  (mmu_coprocessor_setup si.machine2 guest2) 	==>
  (one_step_real sr cycle <|proc:=0|> = (ValueState a sr',rc)) ==>
  (one_step_ideal si cycle <|proc:=0|> = (ValueState a' si',ic,mode')) ==>
  (correct_user_mode_states sr si g) ==>
  (ARM_MODE sr' <> 16w) ==>
  (kth_hyp_invariants sr')   
    ``,
  RW_TAC (srw_ss()) [unique_guest_def, candidate_relation_def]
   	 
     	 THEN IMP_RES_TAC correct_usermode_states_mode_assert_thm
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``, ``sr':arm_state``,  ``si:composite_arm_state``,``a:unit``,
	  ``cycle:int``, 
	  ``rc:int``,``guest1``] outer_switched_mode_thm
	 THEN ASSUME_SPECL_TAC 	
	 [``sr:arm_state``, 
	  ``sr':arm_state``, ``si:composite_arm_state``,``a:unit``,
	  ``cycle:int``, 
	  ``rc:int``,``guest2``]  outer_switched_mode_thm
	 THEN UNDISCH_ALL_TAC
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN RW_TAC (srw_ss()) []	
 );

(**********************************************************)
(*           proof of going to the bisimilar states       *)
(*        after handling the exp/intr by the hypervisor   *)
(**********************************************************)
(* e (RW_TAC bool_ss [candidate_relation_def]); *)
(* if two bisimilar states make transition, they go to the correct switched states *)


fun super_bisim_states_ValueState_tac_list gst = 
 FULL_SIMP_TAC (srw_ss()) [candidate_relation_def,
			   outer_full_relation_user_def]
	
	THEN ASSUME_SPECL_TAC
	[``sr:arm_state``,
	  ``sr':arm_state``,  ``si:composite_arm_state``,``ra:unit``,
	  ``c:int``, 
	  ``rc:int`` ,gst] outer_switched_mode_thm
	THEN UNDISCH_ALL_TAC
	THEN FULL_SIMP_TAC (srw_ss()) []
	THEN RW_TAC (srw_ss()) []
	THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``, ``si:composite_arm_state``,
	  ``sr':arm_state``, ``si':composite_arm_state``,
	  ``si'':composite_arm_state``,
	  ``ib:string``, ``ic:int``, ``ic':int``, 
	  gst, `` ARM_MODE sr'``, ``im':bool[5]``
	 ] super_mode_thm
	THEN TRY (`(transform_state_ideal si' ic (ARM_MODE sr') <|proc := 0|> =
        (ValueState ib si'',ic',im'))` by METIS_TAC [])
	THEN UNABBREV_ALL_TAC
	THEN UNDISCH_ALL_TAC
	THEN FULL_SIMP_TAC (srw_ss()) []
	
	THEN RW_TAC (srw_ss()) []
;


val super_bisim_states_ValueState_thm = store_thm(
  "super_bisim_states_ValueState_thm",
  `` ! sr sr' sr'' si si' si'' 
       c ic ic' rc rc' im im' 
       rm g ra ia rb ib .
  (unique_guest g) ==>
  (one_step_real sr c <|proc:=0|> = (ValueState ra sr',rc)) ==>
  (one_step_ideal si c <|proc:=0|> = (ValueState ia si',ic,im)) ==>
  (candidate_relation (sr,c) (si,c) g) ==>
  (ARM_MODE sr' <> 16w) ==>
  (transform_state_real sr' rc g <|proc:=0|> = (ValueState rb sr'',rc',rm)) ==>
  (transform_state_ideal si' ic im <|proc:=0|> = (ValueState ib si'',ic',im')) ==> 
  ((rc' = ic') /\ (let g'= if (ARM_MODE sr' <>18w) 
				   then g else (if(g=guest1) then guest2 else guest1)
			   in
		       candidate_relation (sr'',rc') (si'',ic') g'))``,
 RW_TAC (srw_ss()) [unique_guest_def]
     THEN IMP_RES_TAC  bisimilar_correct_usermode_states
     THEN IMP_RES_TAC  bisimilar_mode_assert_thm
     THEN FIRST_PROVE 
     [  super_bisim_states_ValueState_tac_list ``guest1``,
	      super_bisim_states_ValueState_tac_list ``guest2``]
); 


(**********************************************************)
(**********************************************************)
(*                     proof of FALSE                     *)
(**********************************************************)
(**********************************************************)

(*     FALSE HANDLERS *)

(* (ideal=error /\ real=valuestate) *)


val super_Error_ideal_ValueState_real_thm = store_thm(
  "super_Error_ideal_ValueState_real_thm",
  `` ! rs rs' rs'' is is' is'' c rc ic rc' ic' 
	im im' rm' g ra ia rb ie  .
   ~( (unique_guest g) /\ 
      (one_step_real rs c  <|proc:=0|> = (ValueState ra rs',rc)) /\
      (one_step_ideal is c  <|proc:=0|> = (ValueState ia is',ic,im)) /\
      (candidate_relation (rs,c) (is,c) g) /\
      (ARM_MODE rs' <> 16w) /\
      (transform_state_real rs' rc g  <|proc:=0|> = (ValueState rb rs'',rc',rm')) /\
      (transform_state_ideal is' ic im  <|proc:=0|> = (Error ie ,ic',im'))) ``,
  let 
      val specl = [``rs:arm_state``,``rs':arm_state``, 
		       ``c:int``,``rc:int``,``ic:int``,
		       ``is:composite_arm_state``, ``is':composite_arm_state``,
		       ``im:bool[5]``, ``g:bool[32]``,
		       ``ra:unit``, ``ia:string``
		      ]
  in
      RW_TAC (srw_ss()) []
      THEN CCONTR_TAC 
      THEN FULL_SIMP_TAC (bool_ss) [(* unique_guest_def *)] 
      THEN FULL_SIMP_TAC (srw_ss()) [candidate_relation_def,
				     outer_full_relation_user_def]
      
      THEN IMP_RES_SPECL_TAC specl correct_switched_mode_in_switched_mode_thm
      THEN IMP_RES_SPECL_TAC specl mmu_setup_in_switched_mode_thm
      THEN IMP_RES_SPECL_TAC specl kth_hyp_invars_in_switched_mode_thm
      THEN IMP_RES_SPECL_TAC specl same_elapsed_cycle_in_switched_mode_thm
      THEN  ASSUME_SPECL_TAC 
      [``rs:arm_state``, ``is:composite_arm_state``,
       ``rs':arm_state``, ``is':composite_arm_state``,
        ``ie:string``,
       ``ic:int``, ``ic':int``, ``g:bool[32]``, 
       ``im:bool[5]``, ``im':bool[5]``
      ] super_mode_error_thm
      THEN FULL_SIMP_TAC (srw_ss()) [unique_guest_def]
      THEN UNDISCH_ALL_TAC
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN RW_TAC (srw_ss()) []
  end	
);





(******************************************************************************)
(*                                                                            *)
(*                     (*  FALSE HANDLERS *)                                  *)
(*                                                                            *)
(******************************************************************************)

(* (ideal=valuestate /\ real=error) *)

val super_ValueState_ideal_Error_real_thm = store_thm(
   "super_ValueState_ideal_Error_real_thm",
  ``  ! rs rs' is is' is'' cycle rc rc' ic ic' 
	im im' rm' g ra ia ib re .
   ~( (unique_guest g) /\ 
      (one_step_real rs cycle  <|proc:=0|> = (ValueState ra rs',rc)) /\
      (one_step_ideal is cycle  <|proc:=0|> = (ValueState ia is',ic,im)) /\
      (candidate_relation (rs,cycle) (is,cycle) g) /\
      (* (read_mode rs = 16w) /\ *)
      (ARM_MODE rs' <> 16w) /\
      (transform_state_real rs' rc g  <|proc:=0|> = (Error re,rc',rm')) /\
      (transform_state_ideal is' ic im  <|proc:=0|> = (ValueState ib is'' ,ic',im')))
   ``,
let val specl = [``rs:arm_state``,``rs':arm_state``, 
		       ``cycle:int``,``rc:int``,``ic:int``,
		       ``is:composite_arm_state``, ``is':composite_arm_state``,
		       ``im:bool[5]``, ``g:bool[32]``,
		       ``ra:unit``, ``ia:string``
		      ]
  in
 RW_TAC (srw_ss()) []
      THEN CCONTR_TAC 
      THEN FULL_SIMP_TAC (bool_ss) [(* unique_guest_def *)] 
      THEN FULL_SIMP_TAC (srw_ss()) [candidate_relation_def,
				     outer_full_relation_user_def]
      
      THEN IMP_RES_SPECL_TAC  
      [``rs:arm_state``,``rs':arm_state``, 
       ``cycle:int``,``rc:int``,``ic:int``,
       ``is:composite_arm_state``, ``is':composite_arm_state``,
       ``im:bool[5]``, ``g:bool[32]``,
       ``ra:unit``, ``ia:string``
      ]  correct_switched_mode_in_switched_mode_thm
      THEN IMP_RES_SPECL_TAC specl mmu_setup_in_switched_mode_thm
      THEN IMP_RES_SPECL_TAC specl kth_hyp_invars_in_switched_mode_thm
      THEN IMP_RES_SPECL_TAC specl same_elapsed_cycle_in_switched_mode_thm
      THEN ASSUME_SPECL_TAC
           [``rs:arm_state``, ``is:composite_arm_state``,
       ``rs':arm_state``, ``is':composite_arm_state``,``is'':composite_arm_state``,
       ``ib:string``, ``rc:int``, ``ic':int``,``g:bool[32]``,
       ``im:bool[5]``, ``im':bool[5]``
      ] super_mode_thm
	   THEN FULL_SIMP_TAC (srw_ss()) [unique_guest_def]
      THEN UNDISCH_ALL_TAC
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN RW_TAC (srw_ss()) []
end
);

(**********************************************************)
(*      handlers: proof of going to the same error state             *)
(**********************************************************)

val super_equal_Error_ideal_Error_real_thm = store_thm(
   "super_equal_Error_ideal_Error_real_thm",
  ``! rs rs' is is' c rc rc' ic ic' 
	im im' rm' g ra ia re ie .
      (unique_guest g) ==>
      (one_step_real rs c  <|proc:=0|> = (ValueState ra rs',rc)) ==>
      (one_step_ideal is c  <|proc:=0|> = (ValueState ia is',ic,im)) ==>
      (candidate_relation (rs,c) (is,c) g) ==>
      (ARM_MODE rs' <> 16w) ==>
      (transform_state_real rs' rc  g  <|proc:=0|> = (Error re,rc',rm')) ==>
      (transform_state_ideal is' ic im  <|proc:=0|> = (Error ie ,ic',im')) ==>
      (re=ie)``,
let val specl = [``rs:arm_state``,``rs':arm_state``, 
		 ``c:int``,``rc:int``,``ic:int``,
		 ``is:composite_arm_state``, ``is':composite_arm_state``,
		 ``im:bool[5]``, ``g:bool[32]``,
		 ``ra:unit``, ``ia:string``
		]
in
 RW_TAC (srw_ss()) []
      THEN CCONTR_TAC 
      THEN FULL_SIMP_TAC (bool_ss) [(* unique_guest_def *)] 
      THEN FULL_SIMP_TAC (srw_ss()) [candidate_relation_def,
				     outer_full_relation_user_def]
      
      THEN IMP_RES_SPECL_TAC  
      [``rs:arm_state``,``rs':arm_state``, 
       ``c:int``,``rc:int``,``ic:int``,
       ``is:composite_arm_state``, ``is':composite_arm_state``,
       ``im:bool[5]``, ``g:bool[32]``,
       ``ra:unit``, ``ia:string``
      ]  correct_switched_mode_in_switched_mode_thm
      THEN IMP_RES_SPECL_TAC specl mmu_setup_in_switched_mode_thm
      THEN IMP_RES_SPECL_TAC specl kth_hyp_invars_in_switched_mode_thm
      THEN IMP_RES_SPECL_TAC specl same_elapsed_cycle_in_switched_mode_thm
      THEN ASSUME_SPECL_TAC
           [``rs:arm_state``, ``is:composite_arm_state``,
       ``rs':arm_state``, ``is':composite_arm_state``, ``ie:string``,
       ``ic:int``, ``ic':int``, ``g:bool[32]``,
       ``im:bool[5]``, ``im':bool[5]``
      ] super_mode_error_thm
	   THEN FULL_SIMP_TAC (srw_ss()) [unique_guest_def]
      THEN UNDISCH_ALL_TAC
      THEN FULL_SIMP_TAC (srw_ss()) []
      THEN RW_TAC (srw_ss()) []
end
					     );





val user_Error_ideal_ValueState_real_thm = store_thm(
  "user_Error_ideal_ValueState_real_thm",
  ``! sr sr' si c rc ic  im g a e .
  ~((unique_guest g) /\ 
  (one_step_real sr c <|proc:=0|> = (ValueState a sr',rc)) /\
  (one_step_ideal si c <|proc:=0|> = (Error e ,ic,im)) /\
  (candidate_relation (sr,c) (si,c) g))``, 
 RW_TAC (srw_ss()) []
	 THEN CCONTR_TAC 
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN IMP_RES_TAC  bisimilar_correct_usermode_states
	 THEN IMP_RES_TAC  bisimilar_mode_assert_thm
	 THEN FULL_SIMP_TAC (srw_ss()) [candidate_relation_def,unique_guest_def,outer_full_relation_user_def]
	 THEN RW_TAC (srw_ss()) []
	 THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``,``sr':arm_state``, ``si:composite_arm_state``, 
	``c:int``, ``a:unit``,
	``rc:int``,``guest1``] outer_user_mode_thm
	 THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``,``sr':arm_state``, ``si:composite_arm_state``, 
	``c:int``, ``a:unit``,
	``rc:int``,``guest2``] outer_user_mode_thm
	 THEN  UNDISCH_ALL_TAC
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN RW_TAC (srw_ss()) []
					   );


val user_ValueState_ideal_Error_real_thm = store_thm(
  "user_ValueState_ideal_Error_real_thm",
  ``! sr si si'  c rc ic  mode' g a er.
  ~( (unique_guest g) /\ 
  (one_step_real sr c <|proc := 0|> = (Error er ,rc)) /\
  (one_step_ideal si c <|proc := 0|> = (ValueState a si',ic,mode')) /\
  (candidate_relation (sr,c) (si,c) g))``, 
  RW_TAC (srw_ss()) []
	 THEN CCONTR_TAC 
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN IMP_RES_TAC  bisimilar_correct_usermode_states
	 THEN IMP_RES_TAC  bisimilar_mode_assert_thm
	 THEN FULL_SIMP_TAC (srw_ss()) [candidate_relation_def,unique_guest_def
				      ,outer_full_relation_user_def]
	 THEN RW_TAC (srw_ss()) []
	 THEN ASSUME_SPECL_TAC [``sr:arm_state``,``guest1``] mmu_setup_implies_mmu_req_thm
	 THEN ASSUME_SPECL_TAC [``sr:arm_state``,``guest2``] mmu_setup_implies_mmu_req_thm
	 THEN ASSUME_SPECL_TAC [``si.machine1:arm_state``,``guest1``] mmu_setup_implies_mmu_req_thm
	 THEN ASSUME_SPECL_TAC [``si.machine2:arm_state``,``guest2``] mmu_setup_implies_mmu_req_thm
  	 THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``, ``si:composite_arm_state``,
	  ``c:int``,``guest1``, ``er:string``,
	  ``rc:int``] user_mode_error_thm
	 THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``, ``si:composite_arm_state``,
	  ``c:int``,``guest2``, ``er:string``,
	  ``rc:int``] user_mode_error_thm
	 THEN  UNDISCH_ALL_TAC
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN RW_TAC (srw_ss()) []
					   );


(******************************************************************************)
(* USER MODE: THE SAME ERROR HAPPENS IN BOTH WORLDS *)
(******************************************************************************)

val user_equal_Error_ideal_Error_real_thm = store_thm(
   "user_equal_Error_ideal_Error_real_thm",
  ``! sr si c rc ic   mode' g er ei .
  (unique_guest g) ==>
  (one_step_real sr c  <|proc := 0|> = (Error er,rc)) ==>
  (one_step_ideal si c  <|proc := 0|> = (Error ei,ic,mode')) ==>
  (candidate_relation (sr,c) (si,c) g) ==>  
  (er = ei)``,
RW_TAC (srw_ss()) []
	 THEN IMP_RES_TAC  bisimilar_correct_usermode_states
	 THEN IMP_RES_TAC  bisimilar_mode_assert_thm
	 THEN FULL_SIMP_TAC (srw_ss()) [candidate_relation_def,unique_guest_def,
					outer_full_relation_user_def]
	 THEN RW_TAC (srw_ss()) []
	 THEN ASSUME_SPECL_TAC [``sr:arm_state``,``guest1``] mmu_setup_implies_mmu_req_thm
	 THEN ASSUME_SPECL_TAC [``sr:arm_state``,``guest2``] mmu_setup_implies_mmu_req_thm
	 THEN ASSUME_SPECL_TAC [``si.machine1:arm_state``,``guest1``] mmu_setup_implies_mmu_req_thm
	 THEN ASSUME_SPECL_TAC [``si.machine2:arm_state``,``guest2``] mmu_setup_implies_mmu_req_thm
 	 THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``, ``si:composite_arm_state``,
	  ``c:int``,``guest1``, ``er:string``,
	  ``rc:int``] user_mode_error_thm
	 THEN ASSUME_SPECL_TAC
	 [``sr:arm_state``, ``si:composite_arm_state``,
	  ``c:int``,``guest2``, ``er:string``,
	  ``rc:int``] user_mode_error_thm
	 THEN  UNDISCH_ALL_TAC
	 THEN FULL_SIMP_TAC (srw_ss()) []
	 THEN RW_TAC (srw_ss()) []  );




fun prove_trans_bisim gst =
    Cases_on `rw_state` THEN Cases_on `iw_state`
	     THEN RW_TAC (srw_ss()) [] 
	     THEN FIRST_PROVE
	     [
	      FULL_SIMP_TAC (srw_ss()) [candidate_relation_def,
					outer_full_relation_user_def]
			    
			    THEN ASSUME_SPECL_TAC  
			    [``rs:arm_state``,``b:arm_state``, 
			     ``cycle:int``,``rc:int``,``ic:int``,
			     ``is:composite_arm_state``, ``b':composite_arm_state``,
			     ``im:bool[5]``, gst,
			     ``a:unit``, ``a':string``
			    ] switched_identical_mode_ValueState_states_thm
			    THEN UNDISCH_ALL_TAC
			    THEN FULL_SIMP_TAC (srw_ss()) []
			    
			    THEN RW_TAC (srw_ss()) []
	    ,
	    ASSUME_SPECL_TAC  
		[``rs:arm_state``,``b:arm_state``, ``b'':arm_state``, 
		 ``is:composite_arm_state``,``b':composite_arm_state``, ``b''':composite_arm_state``, 
		 ``cycle:int``,``ic:int``,``ic':int``,``rc:int``,``rc':int``,
		 ``im:bool[5]``, ``im':bool[5]``,``rm':bool[5]``,
		 gst,  ``a:unit``, ``a':string``,
		 ``a'':unit``, ``a''':string``
		] super_bisim_states_ValueState_thm
		
		THEN (`rc'=ic'` by METIS_TAC [])
		THEN METIS_TAC []
	    ,
	    IMP_RES_SPECL_TAC  
		[``rs:arm_state``,``b:arm_state``, ``b'':arm_state``, 
		 ``is:composite_arm_state``,``b':composite_arm_state``, ``b''':'a``, 
		 ``cycle:int``,``rc:int``,``rc':int``,``ic:int``,``ic':int``,
		 ``im:bool[5]``, ``im':bool[5]``,``rm':bool[5]``,
		 ``g:bool[32]``,  ``a:unit``, ``a':string``,
		 ``a'':unit``, ``s:string``
		] super_Error_ideal_ValueState_real_thm 
	    ,
	    IMP_RES_SPECL_TAC  
		[``rs:arm_state``,``b:arm_state``,
		 ``is:composite_arm_state``,``b':composite_arm_state``, ``b''':composite_arm_state``, 
		 ``cycle:int``,``rc:int``,``rc':int``,``ic:int``,``ic':int``,
		 ``im:bool[5]``, ``im':bool[5]``,``rm':bool[5]``,
		 ``g:bool[32]``,  ``a:unit``, ``a':string``,
		 ``a'':string``, ``s:string``
		] super_ValueState_ideal_Error_real_thm 
	    ,
	    IMP_RES_SPECL_TAC  
		[``rs:arm_state``,``b:arm_state``,
		 ``is:composite_arm_state``,``b':composite_arm_state``,  
		 ``cycle:int``,``rc:int``,``rc':int``,``ic:int``,``ic':int``,
		 ``im:bool[5]``, ``im':bool[5]``,``rm':bool[5]``,
		 ``g:bool[32]``,  ``a:unit``, ``a':string``,
		 ``s:string``, ``s':string``
		] super_equal_Error_ideal_Error_real_thm
		THEN RW_TAC (srw_ss()) []]

fun prove_bisim_theorem gst =
    Cases_on `rs_state` 
	     THEN Cases_on `is_state` 
	     THEN RW_TAC (srw_ss()) [] 
	     THEN Cases_on `rm = 16w` 
	     THEN UNABBREV_ALL_TAC 
	     THEN RW_TAC (srw_ss()) []
	     THENL 
	     [
	      ASSUME_SPECL_TAC  [``rs:arm_state``,``b:arm_state``, 
				 ``cycle:int``,``rc:int``,``ic:int``,
				 ``is:composite_arm_state``, ``b':composite_arm_state``,
				 ``im:bool[5]``, gst,
				 ``a:unit``, ``a':string``
				] user_bisim_states_ValueState_thm
				THEN RW_TAC (srw_ss()) []
	    ,
	    ASSUME_SPECL_TAC [``rs:arm_state``,``b:arm_state``, 
			      ``cycle:int``,``rc:int``,``ic:int``,
			      ``is:composite_arm_state``, ``b':composite_arm_state``,
			      ``im:bool[5]``, gst,
			      ``a:unit``, ``a':string``
			     ] user_identical_mode_ValueState_states_thm
			     THEN RW_TAC (srw_ss()) []
	    ,
	    ASSUME_SPECL_TAC [``rs:arm_state``,``b:arm_state``, 
			      ``cycle:int``,``rc:int``,``ic:int``,
			      ``is:composite_arm_state``, ``b':composite_arm_state``,
			      ``im:bool[5]``, gst,
			      ``a:unit``, ``a':string``
			     ] user_same_elapsed_cycle_ValueState_states_thm
			     THEN RW_TAC (srw_ss()) []
	    ,
	    prove_trans_bisim gst
	    ,
	    IMP_RES_SPECL_TAC  
		[``rs:arm_state``,``b:arm_state``,``is:composite_arm_state``,
		 ``cycle:int``,``rc:int``, ``ic:int``,
		 ``im:bool[5]``, 
		 ``g:bool[32]``,  ``a:unit``, 
		 ``s:string``]
		user_Error_ideal_ValueState_real_thm
	      ,
	      IMP_RES_SPECL_TAC  
		  [``rs:arm_state``,``b:arm_state``,``is:composite_arm_state``,
		   ``cycle:int``,``rc:int``, ``ic:int``,
		   ``im:bool[5]``, 
		   ``g:bool[32]``,  ``a:unit``, 
		   ``s:string``]
		  user_Error_ideal_ValueState_real_thm
		,
		IMP_RES_SPECL_TAC  
		    [``rs:arm_state``,``is:composite_arm_state``,``b:composite_arm_state``,
		     ``cycle:int``,``rc:int``, ``ic:int``,
		     ``im:bool[5]``, 
		     ``g:bool[32]``,  ``a:string``, 
		     ``s:string``]
		    user_ValueState_ideal_Error_real_thm
		  ,
		  IMP_RES_SPECL_TAC  
		      [``rs:arm_state``,``is:composite_arm_state``,``b:composite_arm_state``,
		       ``cycle:int``,``rc:int``, ``ic:int``,
		       ``im:bool[5]``, 
		       ``g:bool[32]``,  ``a:string``, 
		       ``s:string``]
		      user_ValueState_ideal_Error_real_thm
		    ,
		    IMP_RES_SPECL_TAC  
			[``rs:arm_state``,``is:composite_arm_state``,
			 ``cycle:int``,``rc:int``, ``ic:int``,
			 ``im:bool[5]``, 
			 ``g:bool[32]``,  ``s:string``, 
			 ``s':string``]
			user_equal_Error_ideal_Error_real_thm
		      ,
		      IMP_RES_SPECL_TAC  
			  [``rs:arm_state``,``is:composite_arm_state``,
			   ``cycle:int``,``rc:int``, ``ic:int``,
			   ``im:bool[5]``, 
			   ``g:bool[32]``,  ``s:string``, 
			   ``s':string``]
			  user_equal_Error_ideal_Error_real_thm]

val obs_bisim_thm = 
    store_thm ("obs_bisim_thm",
		   `` !sr0 si0 g c. 
		  (unique_guest g) /\ (candidate_relation  (sr0,c) (si0,c) g) 
		 ==>
		 obs_bisimilar (sr0,c) (si0,c) g <|proc:=0|> ``
		 ,
		 RW_TAC arith_ss [obs_bisimilar_def,obs_bisimulation_rel_def]
			THEN    Q.EXISTS_TAC `candidate_relation`
			THEN RW_TAC arith_ss [obs_bisimulation_rel_def]
			THENL [IMP_RES_TAC related_states_have_same_obs_thm ,
			       prove_bisim_theorem ``guest1``, 
			       IMP_RES_TAC related_states_have_same_obs_thm ,
			       `g=guest2` by (METIS_TAC [unique_guest_def])
					  THEN prove_bisim_theorem ``guest2``]
		  );

