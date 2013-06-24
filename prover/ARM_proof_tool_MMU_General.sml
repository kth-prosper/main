(***************************************************)
(*         A Tool To Reason On ARM Model           *)
(*                    Narges                       *)
(***************************************************)

(* should ask the name of theorem to save *)

fun proof_progress s = TextIO.print s;
val let_ss = simpLib.mk_simpset [boolSimps.LET_ss] ;
val words_ss = simpLib.mk_simpset [wordsLib.WORD_ss];

fun generate_uncurry_abs a =
    case dest_term a of
    	(COMB (c,b))  =>  
	if (same_const c ``UNCURRY``) then
	    let val (LAMB(d,e)) = dest_term b 
		val (e_abs,e_trm) = generate_uncurry_abs  e
	    in
		(List.concat [[d],e_abs], e_trm) 
	    end
	else
	    ([], b)
      | (LAMB(c,b))  =>
	([c] , b) 
      | _ => ([], a);

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
	val (b,c) = if (is_comb (List.nth(d1,0))) 
		    then 
			strip_comb  (List.nth(d1,0))
		    else 
			    strip_comb (List.nth(d1,0))
    in
	List.nth(c,0)
    end

fun prove_simple_action opr a  =
    let 
	val thrm = (DB.fetch "scratch" ((term_to_string (opr)) ^ "_thm"))
	val ut_thrm = (DB.fetch "scratch" ((term_to_string (opr)) ^ "_ut_thm"))
	val _ = proof_progress ("\nTheorem " ^ (term_to_string opr) ^ "_thm is applied!\n ")
	val tacs =  RW_TAC (srw_ss()) [thrm,ut_thrm] 
	val _ = e (tacs)
	val proved_a = top_thm()
	val _ = proofManagerLib.drop()
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
    
fun get_monad_type tp =
    let val (str , [fst , snd]) = dest_type (tp)
	val (str , [tp_type, b]) = dest_type snd
    in
	tp_type
    end;

fun decompose a =
    let val (opr, acs) =    
	    case dest_term a of
		(LAMB (b,c)) => 
	     	strip_comb c
	      | (* (COMB (b,c)) *) _ => 
				   strip_comb a
	val thm_exists =  exists_theorem ("scratch") (term_to_string opr ^ "_thm")
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
		val (a,b) =dest_eq con1
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
    


fun prove a  =
    let 
	val prove_COND_action = 
	 fn (if_part,else_part,condition,a) =>
	    let val _ = proof_progress ("A Conditional action\n\n\n")
		val (if_part_thm,tc) = prove if_part 
		val (else_part_thm,tc') = prove else_part
		val tacs =  (ASSUME_TAC if_part_thm)
				THEN (ASSUME_TAC else_part_thm)
				THEN (IF_CASES_TAC )
				THEN (FULL_SIMP_TAC (srw_ss()) [])
				THEN (FULL_SIMP_TAC (srw_ss()) [])
		val _ = e (tacs)
		val proved_b = top_thm()
		val _ = proofManagerLib.drop()
	    in
		(proved_b, tacs)
	    end
	val prove_composite_action = 
	 fn (l, r, opr, a) =>
	    let val _ = proof_progress ("\n\nProof of the compositional action:\n"^(term_to_string a)^"\n\n")
		val (left_hand_thm ,tc) = prove l 
	  	val (right_hand_thm, tc) = prove r 
	  	val tacs =  (ASSUME_TAC left_hand_thm) THEN (ASSUME_TAC right_hand_thm)
	  	val _ = e (tacs)

		(* get types of left and right operands	 *)
		val l_type = get_monad_type(type_of(l))	
	  	val tacsb =
	  	    if (same_const  opr ``$>>=``)
	  	    then	  	 	
			let val (str , [fst , snd]) = dest_type (type_of(r))
			    val r_type = get_monad_type(snd)
			in
			    ASSUME_TAC (SPECL [l,r] 
					      (INST_TYPE [alpha |-> l_type, 
							  beta  |-> r_type]
							 seqT_preserves_user_relation_thm)) THEN
				       (ASSUME_TAC (SPECL [l,r]
							  (INST_TYPE [alpha |-> l_type, 
								      beta  |-> r_type]
								     seqT_untouching_thm)) THEN
						   RES_TAC) 
				       THEN (RW_TAC (srw_ss()) [])
			end
		    else
	  	 	ASSUME_TAC (SPECL [l,r] 
					  (INST_TYPE [alpha |-> l_type, 
						      beta  |-> get_monad_type (type_of(r))]
						     parT_preserves_user_relation_thm)) THEN
				   (ASSUME_TAC (SPECL [l,r]
						      (INST_TYPE [alpha |-> l_type, 
								  beta  |-> get_monad_type (type_of(r))]
								 parT_untouching_thm)) THEN
					       RES_TAC) 
				   THEN (RW_TAC (srw_ss()) [])
	  	val _ = e (tacsb)
		val thrm = top_thm()
	  	val _ = proofManagerLib.drop()
	    in 
		(thrm,tacs THEN tacsb)
	    end
	val prove_constT_action = 
	 fn (a) =>
	    let 
		val COMB (opr, arg) = dest_term a
		val tac = RW_TAC (srw_ss()) 
				 [(SPEC arg (INST_TYPE [alpha |-> (type_of arg)]
				 		       constT_preserves_user_relation_thm))]
	  	val _ = e (tac)
		val proved_thm = top_thm()
	  	val _ = proofManagerLib.drop()
	    in
	  	(proved_thm, tac)
	    end
	val prove_forT_action = 
	 fn (a) =>
	    let 
		val (opr, [l,r,action]) = strip_comb a
		val (sub_thm , aub_tac) = prove action 
		val (str , [fst , snd]) = dest_type (type_of(action))
		val r_type = get_monad_type(snd)
		val tacs = ASSUME_TAC sub_thm 
				      THEN ASSUME_TAC (SPEC action 
							    (INST_TYPE [alpha |-> r_type] 
forT_preserving_thm))
				      THEN ASSUME_TAC (SPEC action 
							    (INST_TYPE [alpha |-> r_type] 
forT_untouching_thm)) 
				      THEN RW_TAC (srw_ss()) []
		val _ = e (tacs)
		val proved_thm = top_thm()
	  	val _ = proofManagerLib.drop()
	    in
	  	(proved_thm, tacs)
	    end
	val prove_condT_action = 
	 fn (a  ) =>
	    let val (opr, acs) = strip_comb a
	  	val (arg_thm,tc) = prove (List.nth(acs,1))
	  	val tacs =   ASSUME_TAC arg_thm 
					THEN RW_TAC (srw_ss()) [condT_preserves_user_relation_thm]
		val _ = e (tacs)
	  	val proved_thm = top_thm()
	  	val _ = proofManagerLib.drop()
	    in
	  	(proved_thm,tc)
	    end
	val prove_case_body =
	 fn (opt,body,flag) =>
	    let val (body_thm,body_tac) = prove body
		val tacs = if (flag) then
			       CASE_TAC 
			       THEN FULL_SIMP_TAC (srw_ss()) []  
			       THEN1 (ASSUME_TAC body_thm
						 THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def,untouching_def]
						 THEN (FULL_SIMP_TAC (srw_ss()) []))
			   else
			       (ASSUME_TAC body_thm
					   THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def,untouching_def]
					   THEN (FULL_SIMP_TAC (srw_ss()) []))
		val _ = e (tacs)
	    in
		(body_thm, tacs) 
	    end	

	(* TODO: it does not return the tactic list correctly *)
	val prove_case_action =
	 fn (a) =>
	    let val tacs = FULL_SIMP_TAC bool_ss [preserve_relation_mmu_def,untouching_def] THEN CASE_TAC 
		val _ = e (tacs)
		val (case_tag, case_options) = TypeBase.strip_case a	  
	    in 
		if (List.length(top_goals()) =2)
		then
		    let val _ = proofManagerLib.backup()
			val cases = tl ((List.rev(case_options))) 
			val proved_cases = 
			    map (fn (opt, body) => prove_case_body (opt, body,true)) cases
			val (opt , body) = hd(List.rev(case_options))
			val (body_thm,body_tac) = prove body
			val tacsb = (ASSUME_TAC body_thm
						THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def,untouching_def]
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
		 let  val proved_cases = map (fn (opt, body) => prove_case_body (opt, body,false)) case_options
		      val (proved_thm) = top_thm()
		      val _ = proofManagerLib.drop()			 
		 in
		     (proved_thm, NO_TAC) 
		 end
	    end

	val analyze_action =
	 fn (a, l , r, opr) =>
	    if ((same_const  opr ``$>>=``) orelse
		(same_const  opr ``$|||``))
	    then
		prove_composite_action (l, r, opr ,a)
	    else
		if (same_const  opr ``COND``) then
	  	    let 
			val (opr, acs) = strip_comb a
	  		val (if_part,else_part) =  (List.nth(acs,1),List.nth(acs,2)) 
		    in
	  		prove_COND_action (if_part, else_part,List.nth(acs,0),a)
	  	    end
		else
	  	    if (same_const  opr ``constT``) then	    
			prove_constT_action (a)
		    else  if (same_const  opr ``forT``) then	    
			prove_forT_action a
		    else 
			if (TypeBase.is_case a)	then 
			    prove_case_action a
			else
			    let val _ = proof_progress ("\n\nProof of a simple action:\n "^(term_to_string l)^"\n\n")
					
  	  			val thm_exist = exists_theorem ("scratch") (term_to_string l ^ "_thm") in
	  			if (thm_exist)
	  			then
	  			    prove_simple_action l a
	  			else
	  			    prove_condT_action (a)
	  		    end
	val prove_abs_action =
	 fn a =>
	    let  val (a_abs,a_body) = pairLib.dest_pabs a
		 val _ =  set_goal([], ``(preserve_relation_mmu_abs ^a) /\ (untouching_abs ^a)``)
		 val _ = e (FULL_SIMP_TAC (let_ss) [])
		 val (proved_a,b) = prove a_body

		 val unbeta_thm= (PairRules.UNPBETA_CONV a_abs a_body)
		 val unbeta_a = mk_comb (a, a_abs)
		 val (str , [fst , snd]) = dest_type (type_of a_body)
		 val (str , [a_body_type, b]) = dest_type snd;

		 val proved_unbeta_lemma = store_thm ("proved_unbeta_lemma",
						      ``(preserve_relation_mmu ^a_body =
							 preserve_relation_mmu (^unbeta_a))
						     ``,
						      (ASSUME_TAC (SPECL [a_body,``^unbeta_a``]
									 (INST_TYPE[alpha |-> a_body_type] first_abs_lemma)))
							  THEN (ASSUME_TAC unbeta_thm)
							  THEN (RES_TAC))

		 val proved_unbeta_ut_lemma = store_thm ("proved_unbeta_ut_lemma",
							 `` (untouching ^a_body = 
							     untouching (^unbeta_a))``,
							 (ASSUME_TAC (SPECL [a_body,``^unbeta_a``]
									    (INST_TYPE[alpha |-> a_body_type] first_abs_ut_lemma)))
							     THEN (ASSUME_TAC unbeta_thm)
							     THEN (RES_TAC))

		 val proved_preserve_unbeta_a =
		     store_thm ("proved_preserve_unbeta_a",
				``(preserve_relation_mmu (^unbeta_a))``,
				(ASSUME_TAC (proved_unbeta_lemma))
				    THEN (ASSUME_TAC proved_a)
				    THEN (FULL_SIMP_TAC (srw_ss()) []))

		 val proved_ut_unbeta_a =
		     store_thm ("proved_ut_unbeta_a",
				``(untouching (^unbeta_a))``,
				(ASSUME_TAC (proved_unbeta_lemma))
				    THEN (ASSUME_TAC proved_a)
				    THEN (FULL_SIMP_TAC (srw_ss()) []))

		 val abs_type = type_of a_abs
		 val (abs_args, abs_body)  = generate_uncurry_abs a		
		 val tacs =  (ASSUME_TAC proved_ut_unbeta_a THEN ASSUME_TAC proved_preserve_unbeta_a)  
		 val gen_preserve_unbeta_thm = generalize_theorem proved_preserve_unbeta_a a 
		 val gen_ut_unbeta_thm = generalize_theorem  proved_ut_unbeta_a  a 
		 val tacs = tacs THEN (ASSUME_TAC gen_preserve_unbeta_thm)
				 THEN (ASSUME_TAC gen_ut_unbeta_thm)
				 THEN (ASSUME_TAC (
				       SPEC a
					    (INST_TYPE [alpha |-> abs_type,
							beta  |-> a_body_type] second_abs_lemma)))
				 THEN (ASSUME_TAC (
				       SPEC a
				 	    (INST_TYPE [alpha |-> abs_type,
				 			beta  |-> a_body_type] second_abs_ut_lemma)))
				 THEN (RW_TAC (srw_ss()) [])
				 THEN (FULL_SIMP_TAC (srw_ss()) [])
		 val _ = e (tacs)
		 val proved_thm = top_thm()
		 val _ = proofManagerLib.drop()
	    in
		(proved_thm,tacs)
	    end

	val prove_simple_unproved_action = 
	 fn (a, opr ) =>
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
					 [preserve_relation_mmu_def,similar_def,readT_def] 
					 THEN  RW_TAC (srw_ss()) [untouching_def]
					 THEN FULL_SIMP_TAC (srw_ss()) [untouched_def, readT_def]
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
			val (c1,d1) = strip_comb con
			val COMB ( tmp , new_a) = dest_term (List.nth(d1,0))
			val (flag, l ,r , opr) = decompose (List.nth (d1,0)) 
			val (proved_a, tacb) =
			    if (flag)
	  		    then
				analyze_action (List.nth (d1,0), l, r, opr)
			    else
	  			let 
				    val (next_proof , next_tac) = prove (new_a)
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
	    prove_abs_action a
	  | COMB (c,b) =>
	    if (same_const c ``UNCURRY``)
	    then
		prove_abs_action a
	    else
		let 
		    val  _ = (set_goal([], ``(preserve_relation_mmu ^a) /\ (untouching ^a)``))
		    val _ = e (FULL_SIMP_TAC (let_ss) [])
  		    val _ = e (FULL_SIMP_TAC (srw_ss()) [])
		    val a' = get_action_from_goal (top_goal())
		    val (flag,l ,r , opr) = decompose a' 
  		in
		    if (flag)
		    then
			analyze_action (a' , l, r, opr)
		    else
			if (same_const opr ``UNCURRY``)
			then
			    prove_abs_action a'
			else
			    prove_simple_unproved_action (a', l)
		end
	  | _ => (ASSUME ``T``, NO_TAC)
    end;



