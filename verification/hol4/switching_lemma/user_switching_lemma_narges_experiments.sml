open arm_astTheory;

val let_ss = simpLib.mk_simpset [boolSimps.LET_ss] ;

val _ = Hol_datatype `error_option = ValueState of 'a => 'b | Error of string`;

val _ = Hol_datatype `state = arm_state
 (*  <| status	    : bool *)
 (* |> *)`;

val _ = type_abbrev("M",``:'b -> ('a, 'b) error_option``);

val constT_def = Define`
  (constT: 'a -> ('a,'b) M) x = \y. ValueState x y`;

val errorT_def = Define`
  (errorT : string -> ('a,'b) M) e = K (Error e)`;

val seqT_def = Define`
  (seqT(* : 'a M -> ('a -> 'b M) -> 'b M *)) s f =
   \y. case s y of Error e -> Error e
                || ValueState z t -> f z t`;

val parT_def = Define`
  (parT(* : 'a M -> 'b M -> ('a # 'b) M *)) s t =
    seqT s (\x. seqT t (\y. constT (x,y)))`;

val parT2_def = Define `
  (parT2: 'a M -> 'a M -> (('a # 'a) # ('a # 'a)) M) s t =
    parT (seqT s (\x. seqT t (\y. constT (x,y))))
         (seqT t (\x. seqT s (\y. constT (x,y))))
`;

(* val lockT_def = Define` *)
(*   (lockT: 'a M -> 'a M) s = s`; *)

val condT_def = Define`
  (condT: bool -> (unit,'b) M -> (unit,'b) M) =
    \b s. if b then s else constT ()`;

val forT_def = tDefine "forT"
 `forT (l : num) (h : num) (f : num -> ('a,'b) M) : (('a list),'b) M =
    if l <= h then
      seqT (f l)
      (\r. seqT (forT (l + 1) h f) (\l. constT (r::l)))
    else
      constT []`
 (WF_REL_TAC `measure (\(l,h,f). h + 1 - l)`);

val readT_def  = Define `(readT f  : ('a,'b) M)   = \y. ValueState (f y) y`;
val writeT_def = Define `(writeT f : (unit,'b) M) = \y. ValueState () (f y)`;

val _ = set_fixity ">>=" (Infixr 660);
val _ = set_fixity "|||" (Infixr 90);
val _ = overload_on(">>=", ``seqT``);
val _ = overload_on("|||", ``parT``);

(**************************** preserve *******************************)

val preserve_relation_def = Define `preserve_relation comp R phi R' phi' =
   ! (s1:state) (s2:state).
     (R s1 s2)            ==>
     (phi s1 )            ==>
     (phi s2)            ==>
     ((?a s1':state s2':state.(
			(comp s1 = ValueState a s1') 
			/\ (comp s2 = ValueState a s2') 
			/\ (R' s1' s2')
			/\ (phi' s1' ) 
			/\ (phi' s2')            
      ))
			\/   (? e. (comp s1 = Error e) /\ (comp s2 = Error e)))`;


val preserve_relation_abs_def = 
    Define `preserve_relation_abs comp R phi R' phi' =
			 ! (s1:state) (s2:state) c.
			   (R s1 s2)            ==>
			   (phi s1 )            ==>
			   (phi s2)            ==>
			   ((?a s1':state s2':state.(
					      (comp c s1 = ValueState a s1') 
					      /\  (comp c s2 = ValueState a s2') 
					      /\ (R' s1' s2')
					      /\ (phi' s1' ) 
					      /\ (phi' s2')     
			    ))
			\/   (? e. (comp c s1 = Error e) /\ (comp c s2 = Error e)))`;

(***********************  basic inference rules  **********************)
(* (! c c'. R' c c' ==> R1 c c') ==> *)
(* (! c c'. (phi' c ==> phi1 c) /\ *)
(*      (phi' c' ==> phi1 c')) ==> *)
(*  (preserve_relation  (f1:'a M) R phi R' phi' )  ==> *)
(*           (preserve_relation_abs (f2:'a -> 'b M) R1 phi1 R2 phi2) ==> *)
(*           (preserve_relation  (seqT f1 f2) R phi R2 phi2) *)

val seqT_preserves_relation_thm = store_thm("seqT_preserves_relation_thm",
``! f1 f2 R R' R''.
 (preserve_relation  (f1:'a M) R phi R' phi' )  ==>
          (preserve_relation_abs (f2:'a -> 'b M) R' phi' R'' phi'') ==>
          (preserve_relation  (seqT f1 f2) R phi R'' phi'')``
,
(RW_TAC (srw_ss()) [seqT_def,constT_def,preserve_relation_def,preserve_relation_abs_def]) 
    THEN (UNDISCH_ALL_TAC
	      THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) []))
    THEN
    UNDISCH_ALL_TAC
    THEN RW_TAC (srw_ss()) []
    THEN FULL_SIMP_TAC (srw_ss()) []
    THEN RES_TAC
    THEN FULL_SIMP_TAC (srw_ss()) []
    THEN PAT_ASSUM ``!s1 s2. R s1 s2 => X`` (fn thm => ASSUME_TAC(SPECL [``s1:state``,``s2:state``] thm))
    THEN RES_TAC
    THEN RW_TAC (srw_ss()) []);

val reflexive_comp_def = Define `reflexive_comp f R =
                       ! s . f s s`; 


val condT_preserves_relation_thm = store_thm("condT_preserves_relation_thm",
``! f1 b R R' . 
	  b ==>
	  (preserve_relation  (f1) R phi R' phi' )  ==>
          (preserve_relation  (condT b f1) R phi R' phi')``
,
(RW_TAC (srw_ss()) [preserve_relation_def,condT_def,
		    constT_def] ) 
THEN (RW_TAC (srw_ss()) [] )
);


val condT_preserves_relation_not_thm = store_thm("condT_preserves_relation_not_thm",
``! f1 b R R' . 
	  ~ b ==>
	  (preserve_relation  (f1) R phi R' phi'  )  ==>
          (preserve_relation  (condT b f1) R phi R phi)``
,
(RW_TAC (srw_ss()) [preserve_relation_def,condT_def,
		    constT_def] ) 
THEN (RW_TAC (srw_ss()) [] )
);

val cond_preserves_relation_thm = store_thm("cond_preserves_relation_thm",
``! f1 b R R' f2 . 
	  (preserve_relation  (f1) R phi R' phi'  )  ==>
	  (preserve_relation  (f2) R phi R' phi'  )  ==>
          (preserve_relation  (if b then f1 else f2) R phi R' phi' )``
,
(RW_TAC (srw_ss()) [preserve_relation_def] ) 
THEN (RW_TAC (srw_ss()) [] )
);


val cond_preserves_relation_b_thm = store_thm("cond_preserves_relation_b_thm",
``! f1 b f2 Rx Ry Rz. 
	  b ==>
	  (preserve_relation  (f1) Rx Ry )  ==>
	  (preserve_relation  (f2) Rx Rz )  ==>
          (preserve_relation  (if b then f1 else f2) Rx Ry)``
,
(RW_TAC (srw_ss()) [preserve_relation_def] ) 
THEN (RW_TAC (srw_ss()) [] )
);

val cond_preserves_relation_notb_thm = store_thm("cond_preserves_relation_notb_thm",
``! f1 b f2 Rx Ry Rz. 
	  ~b ==>
	  (preserve_relation  (f1) Rx Ry )  ==>
	  (preserve_relation  (f2) Rx Rz )  ==>
          (preserve_relation  (if b then f1 else f2) Rx Rz)``
,
(RW_TAC (srw_ss()) [preserve_relation_def] ) 
THEN (RW_TAC (srw_ss()) [] )
);

(* if R and R" are same we don't need to distinguish the conditions as in our case *)

val constT_preserves_relation_thm = store_thm(
    "constT_preserves_relation_thm",
    ``! x R .
 preserve_relation  (constT x) R  R ``,
    RW_TAC (srw_ss()) [constT_def, preserve_relation_def,reflexive_comp_def] THEN 
(RW_TAC (srw_ss()) [] ));


val composite_relation_def =
Define `composite_relation R R' (s:state) (s':state) =
		(R s s') /\ (R' s s')`;	 

(preserve_relation  (f1) R R' )  ==>
(preserve_relation  (f1) (composite_relation R S) (composite_relation R' S))


val parT_preserves_relation_up_thm = store_thm("parT_preserves_relation_up_thm",
    ``! f1 f2 R R' R''. 
          (preserve_relation  (f1) R R' )  ==>
          (preserve_relation (f2) R' R'') ==>
          (preserve_relation  (parT f1 f2) R R'')
	  ``,
   RW_TAC (srw_ss()) [parT_def,seqT_def,constT_def,preserve_relation_def]
	  THEN    UNDISCH_ALL_TAC
       THEN REPEAT (CASE_TAC THEN FULL_SIMP_TAC (srw_ss()) [])
       THEN REPEAT (STRIP_TAC)
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN UNDISCH_ALL_TAC
       THEN RES_TAC
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN PAT_ASSUM ``!s1 s2. R s1 s2 => X`` (fn thm => ASSUME_TAC(SPECL [``s1':state``,``s2':state``] thm))
       THEN PAT_ASSUM ``!s1 s2. R s1 s2 => X`` (fn thm => ASSUME_TAC(SPECL [``s1:state``,``s2:state``] thm))
       THEN UNDISCH_ALL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN FULL_SIMP_TAC (srw_ss()) []
  
(***********************************************************)

val trans_fun_def = Define `trans_fun uf = 
!g st1 st2 st3 .
      (uf g st1 st2) ==>
      (uf g st2 st3) 
      ==>  (uf g st1 st3)`;


