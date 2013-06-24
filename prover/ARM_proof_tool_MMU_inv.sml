(***************************************************)
(*         A Tool To Reason On ARM Model           *)
(*                    Narges                       *)
(***************************************************)

(* should ask the name of theorem to save *)

exception not_matched_pattern; 

fun proof_progress s = TextIO.print s; 
val let_ss = simpLib.mk_simpset [boolSimps.LET_ss] ;
val words_ss = simpLib.mk_simpset [wordsLib.WORD_ss];
val global_mode = ref ``16w:bool[5]``;

fun generate_uncurry_abs a =
    case dest_term a of
    	(COMB (c,b))  =>  
	if (same_const c ``UNCURRY``) then
	    let val (d,e) =
		    case  dest_term b of
			(LAMB(d,e)) => (d,e)
		      | _ => Raise not_matched_pattern 
		val (e_abs,e_trm) = generate_uncurry_abs  e
	    in
		(List.concat [[d],e_abs], e_trm) 
	    end
	else
	    ([], b)
      | (LAMB(c,b))  =>
	([c] , b) 
      | _ => ([], a);


fun get_monad_type tp =
    let val (str , fst , snd) = 
	    case dest_type (tp) of
		(str , [fst , snd]) => (str , fst , snd)
	      | _ => Raise not_matched_pattern 
	val (str , tp_type, b) = 
	    case dest_type snd of
		(str , [tp_type, b]) => (str , tp_type, b)
	      | _ => Raise not_matched_pattern 
    in
	tp_type
    end;
fun generate_uncurry_abs_from_abs a =
    case dest_term a of
    	(LAMB (d,e))  =>  
	let val (e_abs,e_trm) = generate_uncurry_abs_from_abs  e
	in
	    (List.concat [[d],e_abs], e_trm) 
	end
      | _  =>
	([] , a) ;

fun get_action_from_goal g = 
    let val (asm ,con) = g
	val (c1,d1) = strip_comb con
    (* val (c2,d2) = strip_comb (List.nth(d1,0)) *)
    (* val (b,c) = if (is_comb (List.nth(d1,0)))  *)
    (* 	    then  *)
    (* 		strip_comb  (List.nth(d1,0)) *)
    (* 	    else  *)
    (* 		    strip_comb (List.nth(d1,0)) *)
    in
	List.nth(d1,0)
    end

fun get_mode_from_action a = 
    let 
	val (c1,d1) = strip_comb a
	val (c2,d2) = strip_comb (List.nth(d1,1))
	val (c3,d3) = strip_comb (List.nth(d2,0))
    in
	(List.nth(d3,0))
    end;

fun get_invrs_from_goal (asm,con) =
    let	
	val (x,trg_inv) = 
	    case dest_term con of
		COMB(x,trg_inv) => (x,trg_inv) 
	      | _ => Raise not_matched_pattern 

	val (b,src_inv) =
	    case dest_term x of
		COMB(b,src_inv) => 
		(b,src_inv)
	      | _ => Raise not_matched_pattern 
    in
	(src_inv,trg_inv)       
    end;

fun prove_simple_action opr a cm =
    let 
	val  mode_changing_comp = 
	  fn (opr) =>
	     ((same_const opr ``take_undef_instr_exception``) orelse
	      (same_const opr ``take_svc_exception``))
	     
	val (src_inv,trg_inv) = get_invrs_from_goal(top_goal());
	val same_mode =  (term_eq src_inv trg_inv);
	val thrm = 
	    if (same_mode andalso (! global_mode=``16w:bool[5]``)) orelse 
	       (same_const opr ``write_cpsr``) 
	    then
		(DB.fetch  (current_theory()) ((Hol_pp.term_to_string (opr)) ^ "_thm"))
	    else
		(DB.fetch  (current_theory()) ((Hol_pp.term_to_string (opr)) ^ "_comb_thm"))

	val _ =  if (same_mode andalso (! global_mode=``16w:bool[5]``)) 
		 then	
		     proof_progress ("\nTheorem " ^ (term_to_string opr) ^ "_thm is applied!\n ")
		 else
		     proof_progress ("\nTheorem " ^ (term_to_string opr) ^ "_comb_thm is applied!\n ")
      ;

	val tacs =  
	    if (same_const opr ``write_cpsr``)
	    then
		RW_TAC (srw_ss()) [SPECL [``16w:bool[5]``,(get_mode_from_action a )] thrm]
	    else
		if (same_mode orelse (mode_changing_comp opr)) 
		then
		    RW_TAC (srw_ss()) [thrm] 
		else
		    let 
			val thrm = if (same_const opr ``errorT``)
				   then 
				       let 
					   val (c,str) = 
					       case dest_term a of
						   COMB(c,str) => (c,str)
						 |_ => Raise not_matched_pattern 
				       in
					   SPECL [src_inv, str] (
					   INST_TYPE [alpha |-> get_monad_type(type_of(a))] errorT_thm)
				       end
				   else
				       thrm
			val a_thm = SPECL [``assert_mode 16w``, 
					   ``assert_mode ^cm``,
					   trg_inv, ``assert_mode 16w``, a] 
					  (INST_TYPE [alpha |-> get_monad_type(type_of(a))] 
						     preserve_relation_comb_thm1)	
				    
			val _ = proof_progress ("************:\n " 
						^ (term_to_string a) ^ " \n\n"
						^ (term_to_string (concl a_thm)) ^ " \n\n"
						^ (term_to_string (! global_mode)) ^ " \n\n"
						^ (term_to_string cm) ^ " \n\n")
				
			val b_thm = LIST_MP [thrm,
					     SPECL [``16w:bool[5]``, cm] comb_mode_thm] a_thm
		    in
			RW_TAC (srw_ss()) [b_thm] 
		    end

	val _ = e (tacs)
	val proved_a = top_thm()
	val _ = proofManagerLib.drop()

	val cm' = (same_const  opr ``write_cpsr``);
	val new_mode =
	    if (cm')
	    then
		``^cm:bool[5]``
	    else
		!global_mode;
	val () = global_mode := new_mode		 
	val _ = proof_progress ("\nProof of theorem: " ^ (term_to_string a) ^ " is completed!\n ")
    in 
	(proved_a , tacs) 
    end;

fun exists_theorem thy x =
    let val thms = theorems thy
	val thm = List.find (fn (s,t) => (s=x)) thms 
    in
	case thm of
	    SOME (p,q) => true
	  | NONE => false		
    end;
    
fun find_theorem x =
    let val _ = proof_progress ("Searching for the theorem " ^ (x) ^ "\n")
	val db_x = DB.find x
	val res = List.find (fn ((s,t),p) => (t=x)) db_x in
	case  res of
	    SOME ((s,t),(p,q)) =>
	    let val _ = proof_progress ("The theorem " ^ x ^ " was found\n ") in
		p
	    end
	  |NONE =>
	   let val _ = proof_progress ("The theorem " ^ x ^ " was not found\n ") in
	       ASSUME ``T``
	   end
    end;
    

fun decompose a src_inv trg_inv =
    let val (opr, acs) =    
	    case dest_term a of
		(LAMB (b,c)) => 
	     	strip_comb c
	      | (* (COMB (b,c)) *) _ => 
				   strip_comb a

	val thm_exists = if (!global_mode = ``16w:bool[5]`` andalso (term_eq src_inv trg_inv)) orelse
			    ((same_const opr ``write_cpsr``) )
			 then
			     exists_theorem (current_theory()) (term_to_string opr ^ "_thm")
			 else
			     exists_theorem (current_theory()) (term_to_string opr ^ "_comb_thm")

	val flag = ((same_const opr ``$>>=``) orelse
		    (same_const opr ``$|||``) orelse
		    (same_const opr ``constT``) orelse
		    (same_const opr ``COND``) orelse
		    (same_const opr ``condT``) orelse
		    (same_const opr ``forT``) orelse
		    (TypeBase.is_case a ) orelse
		    thm_exists)
    in		     
	if (length acs < 2) then
	    (flag,opr,opr,opr)
	else
	    let val l = List.nth(acs,0) 
		val r = List.nth(acs,1)
	    in			 
		if (same_const opr  (``$>>=``))
		then (flag,l,r,opr)
		else
		    if (same_const opr ``$|||``) then
			(flag,l,r,opr)
		    else (flag,opr,opr,opr)
	    end
    end;
    

(* should be modified to save untouching and preserving lemmas as two separate lemmas*)

fun save_proof name a tacs =
    let val _ = TextIO.print ("Do you like to save the following theorem? \n " ^ (term_to_string (a)) ^ " \n")
	(* val _   = valOf (TextIO.inputLine TextIO.stdIn) *)
	val str = valOf (TextIO.inputLine TextIO.stdIn) 
    in
	case str of 
	    "y\n" =>  
       	    let val _ =  store_thm (((term_to_string (name)) ^ "_thm"), ``preserve_relation_mmu ^a``, tacs) 
	    in
		store_thm (((term_to_string (name)) ^ "_ut_thm"), ``preserve_relation_mmu ^a``, tacs) 
	    end
	  | _ =>  
	    store_thm ("tatulogy", ``T``, DECIDE_TAC) 
    end;

    
(*TODO: use some sort of pattern mathiching instead of list lenght!!!*)
fun get_uncurried_theorem thm l = 
    let val (asm,con) = dest_thm thm
    in
	if( l = 1)
	then
	    thm
	else
	    let  
		val con = concl thm
		val res_thm1 = PairRules.SWAP_PFORALL_CONV con
		val res_thm2 = REWRITE_RULE [res_thm1] thm
		val con1 = concl res_thm1
		val (a,b) = dest_eq con1
		val res_thm3 = PairRules.UNCURRY_FORALL_CONV  b
		val res_thm = REWRITE_RULE [res_thm3] res_thm2
	    in
		get_uncurried_theorem res_thm (l-1)
	    end
    end;

fun generalize_theorem thm a =
    let	 			     
	val (a_abs,a_body) = pairLib.dest_pabs a
	val (abs_args, abs_body)  = generate_uncurry_abs a		
	val generalized_curried_thm =  PairRules.PGENL (List.rev(abs_args)) thm
	val generalized_uncurried_thm =  
	    get_uncurried_theorem generalized_curried_thm (List.length(abs_args))
	val abs_type = type_of a_abs
	val gen_var = (mk_var("y", abs_type))
	val spec_thm= PairRules.PSPEC gen_var generalized_uncurried_thm
	val generalized_thm = GEN  gen_var spec_thm
    in
	generalized_thm
    end;
    
fun build_right_hand_side (r_type, l_type, src_inv, rtrg_inv, ltrg_inv,
			   trg_inv, rsrc_inv, l, r, a, right_hand_thm,mode_changed,cm,flg) =
    let val  (preserve_relation_thm,preserve_relation_v2_thm) =
	     if (flg)
	     then
		 (preserve_relation_comb_abs_thm,
		  preserve_relation_comb_abs_v2_thm)
	     else
		 (preserve_relation_comb_thm,
		  preserve_relation_comb_v2_thm)
    in
	if(mode_changed) 
	then 
	    let val a_thm = SPECL [src_inv, rtrg_inv, trg_inv, ltrg_inv, r] 
				  (INST_TYPE [alpha |-> l_type, beta |-> r_type] 
					     preserve_relation_thm)		
		val b_thm = LIST_MP [right_hand_thm,
				     SPECL [``16w:bool[5]``, cm] comb_mode_thm] a_thm

		val a_thm = SPECL [``assert_mode 16w``, 
				   ``assert_mode ^cm``,
				   trg_inv, ``assert_mode 16w``, r] 
				  (INST_TYPE [alpha |-> r_type] 
					     preserve_relation_comb_thm1)
		val is_write_cpsr = ((String.isSubstring "write_cpsr <|proc := 0|> (cpsr with M :=" 
						      (Hol_pp.term_to_string r))) 
		val b_thm1 =  if (not is_write_cpsr)
			      then
				  LIST_MP [right_hand_thm ,
					   SPECL [``16w:bool[5]``, cm] comb_mode_thm] a_thm
			      else
				  ASSUME ``T``
	    in  
		ASSUME_TAC b_thm 
			   THEN (if(not is_write_cpsr)
				then 
				    ASSUME_TAC b_thm1
				else
				    ALL_TAC)
			   THEN ASSUME_TAC right_hand_thm
			   THEN ASSUME_TAC (SPECL [``16w:bool[5]``, cm ] comb_mode_thm)
			   THEN RES_TAC
			   THEN 
			   (if (flg)
			    then
				ASSUME_TAC (SPECL [l,r,src_inv, ltrg_inv, rtrg_inv, trg_inv]
						  (INST_TYPE [alpha |-> l_type,
							      beta  |-> r_type]
							     seqT_preserves_relation_thm)) 
			    else
				ASSUME_TAC (SPECL [l,r,src_inv, ltrg_inv, rtrg_inv, trg_inv]
						  (INST_TYPE [alpha |-> l_type,
							      beta  |-> get_monad_type (type_of(r))]
							     parT_preserves_relation_thm)))
	    end
	else
	    if (!global_mode = ``16w:bool[5]``)
	    then
		let val invr2 = if (not (term_eq rsrc_inv rtrg_inv)) 
				then
				    ``assert_mode ^cm``				    
				else
				    rtrg_inv
		    val operator_tac = 
			(if(flg) then
			     ASSUME_TAC (SPECL [l,r,src_inv, rsrc_inv, rtrg_inv, rtrg_inv]
					       (INST_TYPE [alpha |-> l_type,
							   beta  |-> r_type]
							  seqT_preserves_relation_thm)) 
   			 else
			     ASSUME_TAC (SPECL [l,r,src_inv, rsrc_inv, rtrg_inv, rtrg_inv]
					       (INST_TYPE [alpha |-> l_type,
							   beta  |-> get_monad_type (type_of(r))]
							  parT_preserves_relation_thm)))
		in
		    ASSUME_TAC right_hand_thm
			       THEN operator_tac
			       THEN
			       (
				if (term_eq src_inv trg_inv) 
				then
				    ASSUME_TAC (SPEC ltrg_inv comb_monot_thm)
				else
				    if(not (term_eq rsrc_inv rtrg_inv)) 
				    then
					ASSUME_TAC (SPECL [``assert_mode 16w``, 
							   ``assert_mode ^cm``,trg_inv ] combv2_thm)
						   THEN  ASSUME_TAC (SPECL [``16w:bool[5]``, cm ] comb_mode_thm)
					
				    else
					(*	     val a_thm = SPECL [``assert_mode 16w``, 
									``assert_mode ^cm``,
									trg_inv, ``assert_mode 16w``, r] 
								       (INST_TYPE [alpha |-> r_type] 
										  preserve_relation_comb_thm1)		
						     val b_thm1 = LIST_MP [right_hand_thm ,
									   SPECL [``16w:bool[5]``, cm] comb_mode_thm] a_thm
					 *)
					ASSUME_TAC (SPEC rtrg_inv comb_monot_thm)
						   THEN ASSUME_TAC right_hand_thm
						   THEN operator_tac 
						   THEN RES_TAC		      
						   THEN PAT_ASSUM ``preserve_relation_mmu ^a x y``
						   (fn thm =>	
						       let val a_thm = SPECL [src_inv, ``assert_mode ^cm``, trg_inv, ltrg_inv, a] 
									     (INST_TYPE [alpha |-> get_monad_type(type_of(a))] 
											preserve_relation_comb_v2_thm)		
							   val _ = proof_progress (" a_thm \n\n"^(term_to_string (concl a_thm))^ 
										   "\nright_hand \n\n"^ (term_to_string (concl right_hand_thm))^ 
										   (term_to_string (concl (SPECL [``16w:bool[5]``, cm] comb_mode_thm))))
							   val b_thm = LIST_MP [thm,
										SPECL [``16w:bool[5]``, cm] comb_mode_thm] a_thm
						       in
							   ASSUME_TAC b_thm 
						       end)
						   THEN ASSUME_TAC (SPECL [``16w:bool[5]``, cm ] comb_mode_thm))
		end
	    else
		ASSUME_TAC (SPEC rtrg_inv comb_monot_thm)
			   THEN ASSUME_TAC (SPECL [src_inv,``(assert_mode ^cm)``, trg_inv] combv2_thm) 
			   THEN ASSUME_TAC right_hand_thm
			   THEN ASSUME_TAC (SPECL [``16w:bool[5]``, cm] comb_mode_thm)
			   THEN 
			   ( if(flg)
			     then 
				 ASSUME_TAC (SPECL [l,r,src_inv, ltrg_inv, rtrg_inv, trg_inv]
						   (INST_TYPE [alpha |-> l_type,
							       beta  |-> r_type]
							      seqT_preserves_relation_thm)) 
			     else
				 ASSUME_TAC (SPECL [l,r,src_inv, ltrg_inv, rtrg_inv, trg_inv]
						   (INST_TYPE [alpha |-> l_type,
							       beta  |-> get_monad_type (type_of(r))]
							      parT_preserves_relation_thm)))
    end 

fun get_type_inst (t, i) = 
    case dest_type (t) of
	(str , [fst , snd]) =>  
	if(i)
	then
	    fst 
	else
	    snd
      |_ => Raise not_matched_pattern; 

fun prove a src_inv trg_inv cm =
    let 
	val prove_COND_action = 
	 fn (if_part,else_part,condition,a,src_inv,trg_inv,cm) =>
	    let val _ = proof_progress ("A Conditional action\n\n\n")
			
		val (if_part_thm,tc) = prove if_part src_inv trg_inv cm;
		val (else_part_thm,tc') = prove else_part src_inv trg_inv cm;
		val tacs =  (ASSUME_TAC if_part_thm)
				THEN (ASSUME_TAC else_part_thm)
				THEN (IF_CASES_TAC )
				THEN (FULL_SIMP_TAC (srw_ss()) [])
				THEN (FULL_SIMP_TAC (srw_ss()) [])
		val _ = e (tacs)
		val proved_b = top_thm()
		val _ = proofManagerLib.drop()
			
		val (flag, if_l ,if_r , if_opr) = decompose if_part src_inv trg_inv
		val (flag, else_l ,else_r , else_opr) = decompose else_part src_inv trg_inv
 	    	val mode_changed = (same_const  if_opr ``take_undef_instr_exception``) orelse
				   (same_const  else_opr ``take_undef_instr_exception``);	
		val new_mode = 
		    if (mode_changed)
		    then
			``^cm:bool[5]``
		    else
			!global_mode;
		val () = global_mode := new_mode;
	    in
		(proved_b, tacs)
	    end
	val prove_composite_action = 
	 fn (l, r, opr, a, src_inv, trg_inv, cm) =>
	    let val _ = proof_progress ("\n\nProof of the compositional action:\n"^(term_to_string a)^"\n\n")
		val _ = proof_progress ("ENTERING:\n global_mode: " ^(term_to_string (! global_mode))^"\n\n"^(term_to_string (a))^"\n\n")
			
		val (lsrc_inv,ltrg_inv) = 
		    if ((String.isSubstring "write_cpsr <|proc := 0|> (cpsr with M :=" 
					    (Hol_pp.term_to_string l))) 
		    then
			(src_inv , trg_inv) 
		    else
			if (not (!global_mode = ``16w:bool[5]``))
			then
			    ( ``comb_mode 16w ^cm`` ,  
			      ``comb_mode 16w ^cm``)
			else
			    ( ``assert_mode ^(!global_mode)`` ,  
			      ``assert_mode ^(!global_mode)``);
		val (left_hand_thm , tc) =   prove l  lsrc_inv ltrg_inv cm;
		val _ = proof_progress ("LEFT PART PROVED:\n global_mode: " ^(term_to_string (! global_mode))^"\n\n"^(term_to_string (l))^"\n\n")
			
		val (f,ll ,lr , oprr) = decompose r src_inv trg_inv;
		val mode_changed = (same_const  oprr ``write_cpsr``)
				   andalso not (term_eq ``write_cpsr <|proc := 0|> (cpsr with IT := 0w)`` r);
		val (rsrc_inv , rtrg_inv ) = 
		    if (mode_changed)
		    then
			(ltrg_inv , ``assert_mode ^(get_mode_from_action r)``)
		    else
			if ((String.isSubstring "write_cpsr <|proc := 0|> (cpsr with M :=" (Hol_pp.term_to_string r)) orelse
			    (String.isSubstring "take_undef_instr_exception" (Hol_pp.term_to_string r))) 
			then
			    (src_inv , trg_inv)
			else
			    if( not (!global_mode = ``16w:bool[5]``))
			    then
				( ``comb_mode 16w ^cm`` ,  
				  ``comb_mode 16w ^cm``)
			    else
				( ``assert_mode ^(!global_mode)`` ,  
				  ``assert_mode ^(!global_mode)``);
		    
  	  	    
		    
		val (right_hand_thm, tc) = prove r  rsrc_inv rtrg_inv cm;
		val _ = proof_progress ("RIGHT PART:\n global_mode: " ^(term_to_string (! global_mode))^"\n\n"^(term_to_string (r))^"\n\n")
			
		val tacs =  (ASSUME_TAC left_hand_thm) 
		val _ = e (tacs)

		(* get types of left and right operands	 *)
		val l_type = get_monad_type(type_of(l))
		val tacsb =
	  	    if (same_const  opr ``$>>=``)
	  	    then	  	 	
			let val snd = get_type_inst (type_of(r) ,false)
			    (*val (str , [fst , snd]) = dest_type (type_of(r))*)
			    val r_type = get_monad_type(snd)
			in
			    build_right_hand_side (r_type, l_type, src_inv, rtrg_inv,  ltrg_inv,
						   trg_inv, rsrc_inv, l , r, a, right_hand_thm, mode_changed,cm,true)
						  THEN RES_TAC
						  THEN (RW_TAC (srw_ss()) [])
			end
		    else
			let val par_rh_tac = build_right_hand_side 
						 (get_monad_type (type_of(r)), l_type, src_inv, rtrg_inv,
						  ltrg_inv, trg_inv, rsrc_inv, l, r, a, right_hand_thm, 
						  mode_changed,cm,false)
			in
	  	 	    ASSUME_TAC (SPEC rtrg_inv comb_monot_thm)
				       THEN  par_rh_tac 
				       THEN RES_TAC
				       THEN (RW_TAC (srw_ss()) [])
			end
	  	val _ = e (tacsb)
		val thrm = top_thm()
	  	val _ = proofManagerLib.drop()
		val _ = proof_progress ("Parameters:\n src_inv: "^(term_to_string src_inv)^"\n\n"
					^"Parameters:\n global_mode: "^(term_to_string (! global_mode))^"\n\n")
	    in 
		(thrm,tacs THEN tacsb)
	    end
	val prove_constT_action = 
	 fn (a,src_inv, trg_inv) =>
	    let 
		val (opr, arg) = 
		    case dest_term a of
			COMB (opr, arg) => (opr, arg)
		      |_ => Raise not_matched_pattern 
		val tac = RW_TAC (srw_ss()) 
				 [(SPECL [src_inv,arg] (INST_TYPE [alpha |-> (type_of arg)]
				 				  constT_preserves_relation_thm))]
	  	val _ = e (tac)
		val proved_thm = top_thm()
	  	val _ = proofManagerLib.drop()
	    in
	  	(proved_thm, tac)
	    end
	val prove_forT_action = 
	 fn (a,src_inv,trg_inv,cm) =>
	    let 
		val (opr, l,r,action) = 
		    case strip_comb a of
			(opr, [l,r,action]) => (opr, l,r,action)
		      |_ => Raise not_matched_pattern 
			    
		val (sub_thm , aub_tac) = prove action src_inv trg_inv cm
		val snd = get_type_inst (type_of(action), false)
		(*val (str , [fst , snd]) = dest_type (type_of(action))*)
		val r_type = get_monad_type(snd)
		val tacs = ASSUME_TAC sub_thm 
				      (*  THEN ASSUME_TAC (SPEC action  *)
				      (* 							    (INST_TYPE [alpha |-> r_type]  *)
				      (* forT_preserving_thm)) *)
				      (* 				       *)
				      THEN RW_TAC (srw_ss()) []
		val _ = e (tacs)
		val proved_thm = top_thm()
	  	val _ = proofManagerLib.drop()
	    in
	  	(proved_thm, tacs)
	    end
	val prove_condT_action = 
	 fn (a,src_inv,trg_inv,cm) =>
	    let val (opr, acs) = strip_comb a
	  	val (arg_thm,tc) = prove (List.nth(acs,1)) src_inv trg_inv cm
	  	val tacs =   ASSUME_TAC arg_thm 
					THEN RW_TAC (srw_ss()) [condT_preserves_relation_thm]
		val _ = e (tacs)
	  	val proved_thm = top_thm()
	  	val _ = proofManagerLib.drop()
	    in
	  	(proved_thm,tc)
	    end
	val prove_case_body =
	 fn (opt,body,flag,src_inv,trg_inv,cm) =>
	    let val (body_thm,body_tac) = prove body src_inv trg_inv cm
		val tacs = if (flag) then
			       CASE_TAC 
				   THEN FULL_SIMP_TAC (srw_ss()) []  
				   THEN1 (ASSUME_TAC body_thm
						     THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]
						     THEN (FULL_SIMP_TAC (srw_ss()) []))
			   else
			       (ASSUME_TAC body_thm
					   THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]
					   THEN (FULL_SIMP_TAC (srw_ss()) []))
		val _ = e (tacs)
	    in
		(body_thm, tacs) 
	    end	

	(* TODO: it does not return the tactic list correctly *)
	val prove_case_action =
	 fn (a ,src_inv,trg_inv,cm) =>
	    let val tacs = FULL_SIMP_TAC bool_ss [preserve_relation_mmu_def] THEN CASE_TAC 
		val _ = e (tacs)
		val (case_tag, case_options) = TypeBase.strip_case a	  
	    in 
		if (List.length(top_goals()) =2)
		then
		    let val _ = proofManagerLib.backup()
			val cases = tl ((List.rev(case_options))) 
			val proved_cases = 
			    map (fn (opt, body) => prove_case_body (opt, body,true,src_inv,trg_inv,cm)) cases
			val (opt , body) = hd(List.rev(case_options))
			val (body_thm,body_tac) = prove body src_inv trg_inv cm
			val tacsb = (ASSUME_TAC body_thm
						THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]
						THEN (FULL_SIMP_TAC (srw_ss()) []  ORELSE METIS_TAC []))
			val _ = e (tacsb)
			val (proved_thm) = top_thm()
			val _ = proofManagerLib.drop()			 
		    in
			(proved_thm, tacs 
					 THEN (foldl (fn ((thm,tac),tacsc) => tacsc THEN tac) (NO_TAC) proved_cases) 
					 THEN tacsb) 
		    end
		else
		    let  val proved_cases = map (fn (opt, body) => prove_case_body (opt, body,false,src_inv, trg_inv,cm)) case_options
			 val (proved_thm) = top_thm()
			 val _ = proofManagerLib.drop()			 
		    in
			(proved_thm, NO_TAC) 
		    end
	    end

	val analyze_action =
	 fn (a, l , r, opr,src_inv,trg_inv,cm) =>
	    if ((same_const  opr ``$>>=``) orelse
		(same_const  opr ``$|||``))
	    then
		prove_composite_action (l, r, opr ,a,src_inv,trg_inv,cm)
	    else
		if (same_const  opr ``COND``) then
	  	    let 
			val (opr, acs) = strip_comb a
	  		val (if_part,else_part) =  (List.nth(acs,1),List.nth(acs,2)) ;
		    in
	  		prove_COND_action (if_part, else_part,List.nth(acs,0),a,src_inv,trg_inv,cm)
	  	    end
		else
	  	    if (same_const  opr ``constT``) then	    
			prove_constT_action (a,src_inv,trg_inv) 
		    else  if (same_const  opr ``forT``) then	    
			prove_forT_action (a,src_inv,trg_inv,cm)
		    else 
			if (TypeBase.is_case a)	then 
			    prove_case_action (a,src_inv,trg_inv,cm)
			else
			    let val _ = proof_progress ("\n\nProof of a simple action:\n "^(term_to_string l)^"\n\n")
					
  	  			val thm_exist = exists_theorem (current_theory()) (term_to_string l ^ "_thm") in
	  			if (thm_exist)
	  			then
	  			    prove_simple_action l a cm
	  			else
	  			    prove_condT_action (a,src_inv,trg_inv,cm)
	  		    end
	val prove_abs_action =
	 fn (a,src_inv,trg_inv,cm) =>
	    let  
		val (a_abs,a_body) = pairLib.dest_pabs a;
		val _ =  set_goal([], ``
				 (preserve_relation_mmu_abs ^a ^src_inv ^trg_inv) ``)
		val _ = e (FULL_SIMP_TAC (let_ss) [])
		val (proved_a,b) = prove a_body src_inv trg_inv cm

		val unbeta_thm= (PairRules.UNPBETA_CONV a_abs a_body)
		val unbeta_a = mk_comb (a, a_abs)
		(*val (str , [fst , snd]) = dest_type (type_of a_body)
		  val (str , [a_body_type, b]) = dest_type snd;*)
		val snd = get_type_inst (type_of(a_body) , false)
		val a_body_type = get_type_inst (snd, true)
				  
		val proved_unbeta_lemma = store_thm ("proved_unbeta_lemma",
						     ``(preserve_relation_mmu ^a_body ^src_inv ^trg_inv=
							preserve_relation_mmu ^unbeta_a ^src_inv ^trg_inv)
						    ``,
						     (ASSUME_TAC (SPECL [a_body,``^unbeta_a``,src_inv,trg_inv]
									(INST_TYPE[alpha |-> a_body_type] first_abs_lemma)))
							 THEN (ASSUME_TAC unbeta_thm)
							 THEN (RES_TAC))

		val proved_preserve_unbeta_a =
		    store_thm ("proved_preserve_unbeta_a",
			       `` (preserve_relation_mmu ^unbeta_a ^src_inv ^trg_inv)``,
			       (ASSUME_TAC (proved_unbeta_lemma))
				   THEN (ASSUME_TAC proved_a)
				   THEN (FULL_SIMP_TAC (srw_ss()) []))

		val abs_type = type_of a_abs
		val (abs_args, abs_body)  = generate_uncurry_abs a		
		val tacs =  (ASSUME_TAC proved_preserve_unbeta_a)  
		val gen_preserve_unbeta_thm = generalize_theorem proved_preserve_unbeta_a a 
		val tacs = tacs THEN (ASSUME_TAC gen_preserve_unbeta_thm)
				THEN (ASSUME_TAC (
				      SPECL[a, src_inv,trg_inv]
					   (INST_TYPE [alpha |-> abs_type,
						       beta  |-> a_body_type] second_abs_lemma)))
				THEN (RW_TAC (srw_ss()) [])
				THEN (FULL_SIMP_TAC (srw_ss()) [])
				THEN (UNDISCH_ALL_TAC THEN 
						      (RW_TAC (srw_ss()) [])
						      THEN (FULL_SIMP_TAC (srw_ss()) []))
		val _ = e (tacs)
		val proved_thm = top_thm()
		val _ = proofManagerLib.drop()
	    in
		(proved_thm,tacs)
	    end

	val prove_simple_unproved_action = 
	 fn (a, opr,cm ) =>
	    let val a_name = opr
		val _ = TextIO.print ("Do you have a theorem to prove " ^ (term_to_string (a)) ^ "  theorem? \n\n")
	    (* val resp = valOf (TextIO.inputLine TextIO.stdIn)  *)
	    in
		(* case resp of  *)
		(*     "y\n" =>   let val _ = TextIO.print ("please enter the name of theorem:\n\n") *)
		(* 		   val thm_name = valOf (TextIO.inputLine TextIO.stdIn) *)
		(* 	       in *)
		(* 		   (find_theorem (substring(thm_name,0,size(thm_name)-1)), NO_TAC) *)
		(* 	       end *)
		(*   | _ => *)	      
		if (same_const  opr ``readT``)
		then
		    let val tac = RW_TAC (srw_ss()) 
					 [preserve_relation_mmu_def,similar_def,readT_def,equal_user_register_def,
					  comb_def,comb_mode_def,assert_mode_def] 
					 THEN FULL_SIMP_TAC (srw_ss()) [untouched_def, readT_def]
					 THEN PAT_ASSUM ``∀ii reg.X`` (fn thm => ASSUME_TAC (SPECL [``<|proc:=0|>``] thm))
					 THEN FULL_SIMP_TAC (srw_ss()) [untouched_def, readT_def] THEN (REPEAT (RW_TAC (srw_ss()) []))
				  
			val _ = e (tac)
	  		val (proved_thm) = top_thm()
			val _ = proofManagerLib.drop()
	  	    in
	  		(proved_thm, tac)
	  	    end
		else 
		    
		    let (* val  _ = (set_goal([], ``preserve_relation ^a``)) *)
			val simp_thm = find_theorem ((term_to_string (opr))^"_def")
			val tacs =  (FULL_SIMP_TAC (srw_ss()) [simp_thm,writeT_def])
			val _ = e (tacs)
	  		val (asm,con) = top_goal()
			val a' = get_action_from_goal (top_goal())
			val (flag,l ,r , opr) = decompose a' src_inv trg_inv
			val (proved_a, tacb) =
			    if (flag)
	  		    then
				analyze_action (a', l, r, opr,src_inv,trg_inv,cm)
			    else
	  			let 
				    val (next_proof , next_tac) = prove a' src_inv trg_inv cm
				    val tac = RW_TAC (srw_ss()) [next_proof]
				    val _ = e (tac)
	  			    val (proved_thm) = top_thm()
				    val _ = proofManagerLib.drop()
	  			in
	  			    (proved_thm, tac)
	  			end
			val tacs = tacs THEN tacb
		    (* val _ = save_proof a_name a (tacs) *)
		    in
			(proved_a, tacs)
		    end
	    end
    in
	case dest_term a of
	    (LAMB (c,b))  =>
	    prove_abs_action (a,src_inv,trg_inv,cm)
	  | COMB (c,b) =>
	    if (same_const c ``UNCURRY``)
	    then
		prove_abs_action (a,src_inv,trg_inv,cm)
	    else
		let val _ = proof_progress ("current action:\n\n"^(term_to_string(a)^ "\n"))
		    val  _ = (set_goal([], `` 
				      preserve_relation_mmu ^a ^src_inv ^trg_inv``))
		    val tac = FULL_SIMP_TAC (let_ss) [] THEN FULL_SIMP_TAC (srw_ss()) []
		    val _ = e (tac)
		   (*  val tac = FULL_SIMP_TAC (srw_ss()) [SPECL [``16w:bool[5]``,!global_mode] read_write_cpsr_thm2, *)
(* SPECL [``16w:bool[5]``,!global_mode] read_write_cpsr_thm3, *)
(* SPECL [``16w:bool[5]``,!global_mode] read_write_cpsr_thm4, *)
(* SPECL [``16w:bool[5]``,!global_mode] read_write_cpsr_thm5, *)
(*  write_cpsr_IT_thm] *)
(* 		THEN TRY *)
(* 					    ( *)
(* 					     ASSUME_TAC (SPECL [``16w:bool[5]``,!global_mode,``sctlr:CP15sctlr``] read_write_cpsr_thm2) *)
(* 							THEN  *)
(* ASSUME_TAC (SPECL [``16w:bool[5]``,!global_mode,``sctlr:CP15sctlr``,``scr:CP15scr``] read_write_cpsr_thm4) *)
(* 							THEN  *)
(* ASSUME_TAC (SPECL [``16w:bool[5]``,!global_mode,``sctlr:CP15sctlr``,``scr:CP15scr``] read_write_cpsr_thm5) *)
(* 							THEN  *)
(* ASSUME_TAC (SPECL [``16w:bool[5]``,!global_mode,``sctlr:CP15sctlr``] read_write_cpsr_thm3) *)
(* 							THEN FULL_SIMP_TAC (srw_ss()) []) *)

(* 		    val _ = e (tac) *)
		in
		    if (can top_thm())
		    then
			let val (proved_thm) = top_thm()
			    val _ = proofManagerLib.drop()
	  		in
	  		    (proved_thm, tac)
	  		end
		    else
			let  val _ = proofManagerLib.b()
			     val a' = get_action_from_goal (top_goal());
			     val (flag,l ,r , opr) = decompose a' src_inv trg_inv;
			in
			    if (flag)
			    then
				analyze_action (a' , l, r, opr,src_inv,trg_inv,cm)
			    else
				if (same_const opr ``UNCURRY``)
				then
				    prove_abs_action (a',src_inv,trg_inv,cm)
				else
				    prove_simple_unproved_action (a', l,cm)
			end
		end
	  | _ => (ASSUME ``T``, NO_TAC)
    end;


























fun prove_abs_action (proved_a,a,src_inv,trg_inv) =
    let  val (a_abs,a_body) = pairLib.dest_pabs a
	 val _ =  set_goal([], ``(preserve_relation_mmu_abs ^a ^src_inv ^trg_inv) ``)

	 val unbeta_thm= (PairRules.UNPBETA_CONV a_abs a_body)
	 val unbeta_a = mk_comb (a, a_abs)
	 val snd = get_type_inst (type_of(a_body) , false)
	 val a_body_type = get_type_inst (snd, true)
			   
	 val proved_unbeta_lemma = store_thm ("proved_unbeta_lemma",
					      ``(preserve_relation_mmu ^a_body ^src_inv ^trg_inv=
						 preserve_relation_mmu ^unbeta_a ^src_inv ^trg_inv)
					     ``,
					      (ASSUME_TAC (SPECL [a_body,``^unbeta_a``,src_inv,trg_inv]
								 (INST_TYPE[alpha |-> a_body_type] first_abs_lemma)))
						  THEN (ASSUME_TAC unbeta_thm)
						  THEN (RES_TAC))

	 val proved_preserve_unbeta_a =
	     store_thm ("proved_preserve_unbeta_a",
			``(preserve_relation_mmu ^unbeta_a ^src_inv ^trg_inv)``,
			(ASSUME_TAC (proved_unbeta_lemma))
			    THEN (ASSUME_TAC proved_a)
			    THEN (FULL_SIMP_TAC (srw_ss()) []))

	 val abs_type = type_of a_abs
	 val (abs_args, abs_body)  = generate_uncurry_abs a		
	 val tacs =  (ASSUME_TAC proved_preserve_unbeta_a)  
	 val gen_preserve_unbeta_thm = generalize_theorem proved_preserve_unbeta_a a 
	 val tacs = tacs THEN (ASSUME_TAC gen_preserve_unbeta_thm)
			 THEN (ASSUME_TAC (
			       SPEC a
				    (INST_TYPE [alpha |-> abs_type,
						beta  |-> a_body_type] second_abs_lemma)))
			 THEN (RW_TAC (srw_ss()) [])
			 THEN (FULL_SIMP_TAC (srw_ss()) [])
	 val _ = e (tacs)
	 val proved_thm = top_thm()
	 val _ = proofManagerLib.drop()
    in
	(proved_thm,tacs)
    end
