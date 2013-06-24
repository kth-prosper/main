load "armLib";
load "stringLib";

(*===============================Global Variables ================================*)
val reg_list = ["r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7", "r8", "r8_fiq",
		"r9", "r9_fiq", "r10", "r10_fiq", "r11", "r11_fiq", "r12", "r12_fiq",
		"sp", "sp_fiq", "sp_irq", "sp_svc", "sp_abt", "sp_und", "sp_mon", "lr",
		"lr_fiq", "lr_irq", "lr_svc", "lr_abt", "lr_und", "lr_mon", "pc"];

val std_reg_list = ["r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7",
		    "r8", "r9", "r10", "r11", "r12", "sp", "sp_svc",
		    "lr", "lr_svc"];

val std_flag_list = ["n_flag","c_flag","z_flag","v_flag","q_flag"(* ,"ge_flag" *),"e_flag", "j_flag", "a_flag", "i_flag", "t_flag", "m_flag", "f_flag",
		     "it_flag"
		    ];

(* ,   , , "f_flag"*)

val hex = Int.fmt StringCvt.HEX;


fun remove_padding s =
    s |> Substring.full
      |> Substring.dropl Char.isSpace
      |> Substring.dropr Char.isSpace
      |> Substring.string;





(* General utility functions *)
fun trimer_ls exp in_1 in_2 =
    let val tmp_res_1 = List.drop (exp,in_1)
        val tmp_res_2 = List.rev tmp_res_1
        val tmp_res_3 = List.drop (tmp_res_2,in_2)
        val fres = List.rev tmp_res_3
    in
        fres
    end;

fun member y []      = false
 |  member y (x::xs) = x=y orelse member y xs;

fun my_eval exp =
    let val th = ASSUME ``tmp_res = ^exp``
	val th = computeLib.RESTR_EVAL_RULE [``read_mem32``] th
	val (_, post) = dest_thm th
	val (_, res) = dest_eq post
    in res
    end;


(* Step related functions *)
fun build_sym_state () =
    let val state = ``
    <| registers := proc 0
    			 (RName_case r0 r1 r2 r3 r4 r5 r6 r7 r8
    			  r8_fiq r9 r9_fiq r10 r10_fiq r11 r11_fiq r12
    			  r12_fiq sp sp_fiq sp_irq sp_svc sp_abt sp_und sp_mon
    			  lr lr_fiq lr_irq lr_svc lr_abt lr_und
    			  lr_mon pc)
       ;
       psrs := proc 0
    	      (PSRName_case
    	       <|
    	        N := n_flag; Z := z_flag; C := c_flag; V := v_flag;
    	        Q := q_flag; IT := 0w;
    	        J := F; Reserved := res_flag;
    	        GE := ge_flag; E := F; A := a_flag;
    	        I := i_flag; F := f_flag; T := F; M := 19w
               |>
               spsr_fiq spsr_irq
    	       <|
    	        N := svc_n_flag; Z := svc_z_flag; C := svc_c_flag; V := svc_v_flag;
    	        Q := svc_q_flag; IT := svc_it_flag;
    	        J := svc_j_flag; Reserved := svc_res_flag;
    	        GE := svc_ge_flag; E := svc_e_flag; A := svc_a_flag;
    	        I := svc_i_flag; F := svc_f_flag; T := svc_t_flag; M := svc_m_flag
               |>
	       spsr_mon spsr_abt spsr_und
    	    )
       ;
       event_register := (K T);
       interrupt_wait := (K F);
       memory := mem;
       accesses := [];
       information := <| arch := arch;
                         unaligned_support := T;
                         extensions := {} |>;
       coprocessors updated_by
         (Coprocessors_state_fupd
            (cp15_fupd (CP15reg_SCTLR_fupd
              (\sctlr. sctlr with <| V := F; A := T; U := F;
                                     IE := T; TE := F; NMFI := T;
                                     EE := T; VE := F |>)) o
             cp14_fupd (CP14reg_TEEHBR_fupd (K 0xF0000000w))));
       monitors := monitors
       |>``
	val state = EVAL state;
	val (_, post) = dest_thm state;
	val (_, state) = dest_eq post;
    in state
    end;

fun step_th_to_exprs step_th  = 
    let val (_, post) = dest_thm step_th
	val (_, post) = markerSyntax.dest_label post
	val (_, imp) = dest_forall post
	val (pre, eq) = dest_imp imp
	val (_, some) = dest_eq eq
	val (exp) = optionSyntax.dest_some some
    in (pre, exp)
    end;

fun apply_exp_to_state exp state  =
    let val exec = ``
	      let state = ^state
	      in ^exp``
	val result = EVAL exec
	val (_, post) = dest_thm result
	val (_, final_state) = dest_eq post
    in final_state
    end;


fun read_reg_worker state rname  =
    let val holr_name = case rname
		     of "r0" => ``RName_0usr:RName``
		      |"r1" => ``RName_1usr:RName``
		      |"r2" => ``RName_2usr:RName``
		      |"r3" => ``RName_3usr:RName``
		      |"r4" => ``RName_4usr:RName``
		      |"r5" => ``RName_5usr:RName``
		      |"r6" => ``RName_6usr:RName``
		      |"r7" => ``RName_7usr:RName``
		      |"r8" => ``RName_8usr:RName``
		      |"r9" => ``RName_9usr:RName``
		      |"r10" => ``RName_10usr:RName``
		      |"sl" => ``RName_10usr:RName``
		      |"fp" => ``RName_11usr:RName``
		      |"r11" => ``RName_11usr:RName``
		      |"ip" => ``RName_12usr:RName``
		      |"r12" => ``RName_12usr:RName``
		      |"sp" => ``RName_SPusr:RName``
		      | "pc" =>  ``RName_PC:RName``
		      | "lr" =>  ``RName_LRusr:RName``
		      |"sp_svc" => ``RName_SPsvc:RName``
		      | "lr_svc" =>  ``RName_LRsvc:RName``
    in EVAL ``case (read__reg <| proc := 0 |> ^holr_name) ^state 
			  of ValueState r s -> r``
    end;

fun read_reg state rname = 
 	let val reg_th = read_reg_worker state rname
	    val (_, post) = dest_thm reg_th
	    val (_, reg) = dest_eq post
	in reg
	end;

fun read_psr state reg =
    my_eval ``case read__psr <| proc := 0 |> ^reg ^state
	       of ValueState cp b -> cp``;

fun read_flag_worker  cpsr index =
	case index of "n_flag" =>  EVAL ``^cpsr.N``
		    | "c_flag" =>  EVAL ``^cpsr.C``
		    | "z_flag" =>  EVAL ``^cpsr.Z``
		    | "v_flag" =>  EVAL ``^cpsr.V``
		    | "t_flag" =>  EVAL ``^cpsr.T``
		    | "q_flag" =>  EVAL ``^cpsr.Q``
		    (* | "ge_flag"=>  EVAL ``^cpsr.GE`` *)
		    | "e_flag" =>  EVAL ``^cpsr.E``
		    | "j_flag" =>  EVAL ``^cpsr.J``
		    | "a_flag" =>  EVAL ``^cpsr.A``
		    | "i_flag" =>  EVAL ``^cpsr.I``
		    | "f_flag" =>  EVAL ``^cpsr.F``
		    | "t_flag" =>  EVAL ``^cpsr.T``
		    | "m_flag" =>  EVAL ``^cpsr.M``
		    | "it_flag" =>  EVAL ``^cpsr.IT``
;

fun read_flag cpsr index =
    let val flag_th = read_flag_worker cpsr index
	val (_, post) = dest_thm flag_th
	val (_, flag) = dest_eq post
    in flag
    end;

fun read_accesses state = 
    let val accesses_th = EVAL ``^state.accesses``
	val (_, post) = dest_thm accesses_th
	val (_, accesses) = dest_eq post
    in accesses
    end;

(* HOL Expression manipulation*)
fun build_condition_from_list lst =
    if (List.null lst) then
	``T``
    else
	list_mk_conj lst
       
fun remove_align_from_condition exp =
    let val exp1 = snd (dest_eq (concl (SIMP_RULE (srw_ss()) [ASSUME (``!x:bool[32].aligned_bx x``)] (ASSUME ``a = ^exp``))))
	val ls = strip_conj exp1
	val fls = trimer_ls ls 0 5
    in
	build_condition_from_list fls
    end;

fun remove_e1_flag_from_condition exp =
    let val ls = strip_conj exp
	val fls = trimer_ls ls 1 0
    in
	build_condition_from_list fls
    end;

(* HOL Expression to IL*)
fun flag_st exp =
    String.map Char.toUpper exp;

fun reg_st exp =
    String.map Char.toUpper exp;
fun is_lamb exp  =
    case dest_term exp
     of LAMB(fname, value) => true
      | _ => false;
fun dest_lamb exp  =
    case dest_term exp
     of LAMB(fname, value) => value
      |_ => `` ``;

(* Never use this function *)
fun exp2ilexp2 exp extend =
    let fun exp2ilexp_inner exp =
	    if (is_lamb exp) then 
 		exp2ilexp_inner(dest_lamb exp)
	    else if is_var exp then
       		let 
		    val (vname, vtype) = dest_var exp in
		    if type_of exp = ``:bool`` then
			(concat [flag_st vname, ":bool"])
		    else if (member vname reg_list andalso (not extend)) then
			(concat [reg_st vname, ":u32"])
		    else if  (member vname reg_list) andalso extend then
			(concat ["extend:u64","(",reg_st vname, ":u32",")"])
		    else if extend then
			(concat ["extend:u64","(",vname,":u32",")"])
		    else
			(concat [flag_st vname,":u32"])
			(* else *)
			(*     concat [vname] *)

		end
	    else if wordsSyntax.is_w2n exp then
		(concat [(*"extend:u64(low:u32(",*)
       			 (exp2ilexp_inner (wordsSyntax.dest_w2n exp) )(*,
								     "))"*)])
	    else if wordsSyntax.is_n2w exp then
       		let val (exp1, vtype) = wordsSyntax.dest_n2w exp in
		    if numSyntax.is_numeral exp1 then
		    	exp2ilexp_inner exp1
		    else
			(concat ["low:u32(",
				 (exp2ilexp_inner exp1),
				 ")"])
		end
	    else if (wordsSyntax.is_word_or exp) then
		let val (or_1,or_2) = wordsSyntax.dest_word_or exp in
		    String.concatWith " | " [exp2ilexp_inner or_1, exp2ilexp_inner or_2]
		end
	    else if numSyntax.is_plus exp then
	    	concat ["(",String.concatWith " + " (map exp2ilexp_inner (numSyntax.strip_plus exp)),")"]

	    else if wordsSyntax.is_word_add exp then
	    	let val (exp1, exp2) = wordsSyntax.dest_word_add exp in
	    	    concat ["(",String.concatWith " + " [exp2ilexp_inner exp1 , exp2ilexp_inner exp2],")"]
	    	end
    	    else if (wordsSyntax.is_word_le exp) then
		let val (le_1, le_2) = wordsSyntax.dest_word_le exp in
		    concat ["(",String.concatWith " <= " [exp2ilexp_inner le_1, exp2ilexp_inner le_2],")"]
		end 
	    else if (wordsSyntax.is_word_lt exp) then
		let val (lt_1, lt_2) = wordsSyntax.dest_word_lt exp in
		    concat ["(",String.concatWith " < " [exp2ilexp_inner lt_1, exp2ilexp_inner lt_2],")"]
		end
	    else if (wordsSyntax.is_word_ge exp) then
		let val (ge_1, ge_2) = wordsSyntax.dest_word_ge exp in
		    concat ["(",String.concatWith " >= " [exp2ilexp_inner ge_1, exp2ilexp_inner ge_2],")"]
		end
	    else if (wordsSyntax.is_word_gt exp) then
		let val (gt_1, gt_2) = wordsSyntax.dest_word_gt exp in
		    concat ["(",String.concatWith "> " [exp2ilexp_inner gt_1, exp2ilexp_inner gt_2],")"]
		end
	    else if wordsSyntax.is_word_1comp exp then
		(concat [" ~",(exp2ilexp_inner (wordsSyntax.dest_word_1comp exp))])
	    else if wordsSyntax.is_word_2comp exp then
		(concat [" -",(exp2ilexp_inner (wordsSyntax.dest_word_2comp exp))])
	    else if wordsSyntax.is_word_and exp then
      		let val (exp1,exp2) = wordsSyntax.dest_word_and exp in
		    concat ["(",String.concatWith " & " [exp2ilexp_inner exp1 , exp2ilexp_inner exp2],")"]
		end
	    else if numSyntax.is_numeral exp andalso (not extend) then
	    	(concat
	    	     ["0x" , (Int.fmt StringCvt.HEX (Arbnumcore.toInt(numSyntax.dest_numeral exp))),
	    	      ":u32"])
	    else if numSyntax.is_numeral exp andalso extend then
		(concat 
		     ["0x" , (Int.fmt StringCvt.HEX (Arbnumcore.toInt(numSyntax.dest_numeral exp))),
		      ":u64"])

	    else if (boolSyntax.is_cond exp) then
		let val (cond_1,cond_2,cond_3) = boolSyntax.dest_cond exp in
		    concat ["( if ",exp2ilexp_inner cond_1," then ",exp2ilexp_inner cond_2," else ", exp2ilexp_inner cond_3,")" ]
		end
	    else if boolSyntax.is_eq exp then
		let val (eq_1, eq_2) = boolSyntax.dest_eq exp in
		    concat ["(",String.concatWith " == " [exp2ilexp_inner eq_1, exp2ilexp_inner eq_2],")"]
		end
	    else if boolSyntax.is_conj exp then
	    	let val (conj_1, conj_2)= boolSyntax.dest_conj exp in
	    	    String.concatWith " & " [exp2ilexp_inner conj_1, exp2ilexp_inner conj_2]
	    	end
	    else if numSyntax.is_less exp then
		let val (ls_1, ls_2)= numSyntax.dest_less exp in 
		    String.concatWith " < " [exp2ilexp_inner ls_1, exp2ilexp_inner ls_2]
		end
	    else if (wordsSyntax.is_word_msb exp) then
		let val mb_1 = wordsSyntax.dest_word_msb exp in
		    (* print_term mb_1; *)
		    (* print_type (type_of mb_1); *)
		    if extend then
			concat ["low:bool((",exp2ilexp_inner mb_1,") >> 0x1f:u64 )"]
		    else
			concat ["low:bool((",exp2ilexp_inner mb_1,") >> 0x1f:u32 )"]
		end
	    else if (wordsSyntax.is_word_lsl exp) then
	    	let val (lsl_1, lsl_2) = wordsSyntax.dest_word_lsl exp in
	    	    concat ["(", String.concatWith " << " [exp2ilexp_inner lsl_1, exp2ilexp_inner lsl_2],")"]
	    	end
	    else if (wordsSyntax.is_word_lsr exp) then
	    	let val (lsl_1, lsl_2) = wordsSyntax.dest_word_lsr exp in
	    	    concat ["(",String.concatWith " >> " [exp2ilexp_inner lsl_1, exp2ilexp_inner lsl_2],")"]
	    	end
	    else if (wordsSyntax.is_word_asr exp) then
		let val (lsl_1, lsl_2) = wordsSyntax.dest_word_asr exp in
		    concat ["(",String.concatWith " $>> " [exp2ilexp_inner lsl_1, exp2ilexp_inner lsl_2],")"]
		end
	    else if (is_neg exp) then
		let val neg_1 = dest_neg exp in
		    concat ["~",exp2ilexp_inner neg_1]
		end
	    else if (boolSyntax.is_disj exp) then
		let val (disj_1, disj_2) = boolSyntax.dest_disj exp in
		    concat ["(",exp2ilexp_inner disj_1, "|", exp2ilexp_inner disj_2, ")"]
		end
	    else if (is_imp exp) then
    		let val (imp_1, imp_2) = dest_imp exp in
    		    concat ["(",String.concatWith " | " [concat ["~","(",(exp2ilexp_inner imp_1),")"], exp2ilexp_inner imp_2],")"]
    		end

	    (* Extract bit k-th of n: (n & ( 1 << k )) >> k *)
	    else if (wordsSyntax.is_index exp) then
		let val (index_1, index_2) = wordsSyntax.dest_index exp in
		    concat ["(", exp2ilexp_inner index_1," & ","(0x1:u32 << ",exp2ilexp_inner index_2,")) >> ", exp2ilexp_inner index_2]
		end

	    (*Bit theory page 85 : |- !b n. BIT b n = ((n DIV 2 ** b) MOD 2 = 1)*)
	    else if (bitSyntax.is_bit exp) then
		let val (bit_1,bit_2) = bitSyntax.dest_bit exp in
		    concat["(((",exp2ilexp_inner bit_2," / (","0x1:u64"," << ", exp2ilexp_inner bit_1,"))"," % ","0x2:u64",")"," == ","0x1:u64",")"]
		end

	    else if (wordsSyntax.is_word_xor exp) then
		let val (xor_1,xor_2) = wordsSyntax.dest_word_xor exp in
		    concat ["(", exp2ilexp_inner xor_1,"^", exp2ilexp_inner xor_2,")"]
		end
	    else if (wordsSyntax.is_word_mul exp) then
		let val (mul_1,mul_2) = wordsSyntax.dest_word_mul exp in
		    concat ["(", exp2ilexp_inner mul_1,"*", exp2ilexp_inner mul_2,")"]
		end

	    (* Extracting more than one bit:  y = (x & ((1 << (m-1)) - (1 << (n-1)))) >> n*)
	    else if (wordsSyntax.is_word_extract exp) then
		let val (ext_1,ext_2,ext_3,_) =  wordsSyntax.dest_word_extract exp in
		    concat ["((",exp2ilexp_inner ext_3 , " & ", 
			    "((0x1:u32 << (",exp2ilexp_inner ext_1 ,"- 0x1:u32)) - (0x1:u32 << (",exp2ilexp_inner ext_2,"- 0x1:u32)))) >>",exp2ilexp_inner ext_2,")"]
		end

	    else if (numSyntax.is_mod exp) then
		let val (mod_1,mod_2) = numSyntax.dest_mod exp in
		    concat ["(",exp2ilexp_inner mod_1," % ",exp2ilexp_inner mod_2,")"]
		end
		
	    else if (is_comb exp) then
		let val (exc_1, exc_2) = strip_comb exp
		in 
		    if(is_const exc_1) then
			let val (cst_name,_) = dest_const exc_1 in
			    case cst_name of "read_mem32" => 
					     let val (mm_str,mm_type) = dest_var (List.nth(exc_2,1))
					     in
					     	 concat [mm_str,":?u32","[",exp2ilexp_inner (List.nth (exc_2,0)),",  e_little]:u32"]
	                                     end
					   |_ =>
					    let val (comb_1,comb_2) = dest_comb exp
						val (cst_name,_) = dest_const comb_1 in
						case cst_name of "aligned" => 
								 let val (_,comb_3) = strip_comb comb_2 in
								     concat ["(",exp2ilexp_inner (hd comb_3)," == ",exp2ilexp_inner (hd(tl comb_3)),"*","(",exp2ilexp_inner (hd comb_3),"$/",exp2ilexp_inner (hd (tl comb_3)),"))"]
								 end
							       | "align" =>
								 let val (_,comb_3) = strip_comb comb_2 in
								     concat ["(",exp2ilexp_inner (hd(tl comb_3)),"*","(",exp2ilexp_inner (hd comb_3),"$/",exp2ilexp_inner (hd (tl comb_3)),"))"]
								 end
							       | "aligned_bx"=>
								 let val m = 1
								     val n = 0 in
								     concat ["((",exp2ilexp_inner comb_2 , " & ", "((0x1:u32 << ( ","0x",Int.fmt StringCvt.HEX m ,":u32","- 0x1:u32)) - (0x1:u32 << ( ","0x",Int.fmt StringCvt.HEX n,":u32","- 0x1:u32)))) >>","0x",Int.fmt StringCvt.HEX n,":u32",")"]
								 end
							       | "LSR_C" => 
								 let val (_,comb_3) = strip_comb comb_2 in
								     concat["(((",exp2ilexp_inner ( hd comb_3)," / ( ","0x2:u32"," << ","(", exp2ilexp_inner (hd (tl comb_3)),"- 0x1:u32 )))","%","0x2:u32",")"," == ","0x1:u32",")"]
								 end
							       | "!" =>
								 let val (comb_11,comb_22) = strip_comb exp in
    	    	    			   			     concat [exp2ilexp_inner (List.nth (comb_22,0))]
								 end
	    	    					       |_ =>  ""
					    end
			end
		    else   let 
			    val (comb_11,comb_22) = dest_comb exp in
			    if (is_var comb_11) then
				let 
				    val (cmb1_name,_) = dest_var comb_11
				    val ext_bool_flag = (
					fn (flag, bits) =>
					   concat [
					   "((extend:u32(",
					   exp2ilexp_inner (my_eval flag),
					   ") << ", bits, ":u32)",
					   "& (0x1:u32 << ",
					   bits, ":u32))"])
				in if cmb1_name = "guancio_psr_to_reg" then
				       concat [
				       "(",
				       ext_bool_flag (``^comb_22.N``, "31"), "|", 
				       ext_bool_flag (``^comb_22.Z``, "30"), "|", 
				       ext_bool_flag (``^comb_22.C``, "29"), "|", 
				       ext_bool_flag (``^comb_22.V``, "28"), "|", 
				       ext_bool_flag (``^comb_22.Q``, "27"), "|", 
				       ext_bool_flag (``^comb_22.J``, "24"), "|", 
				       ext_bool_flag (``^comb_22.E``, "9"), "|", 
				       ext_bool_flag (``^comb_22.A``, "8"), "|", 
				       ext_bool_flag (``^comb_22.I``, "7"), "|", 
				       ext_bool_flag (``^comb_22.F``, "6"), "|", 
				       ext_bool_flag (``^comb_22.T``,"5"),
				       ")"
				       ]
				   else if(String.isPrefix "mem_" cmb1_name ) then
				       if((type_of (comb_11) = ``:bool[32]->bool[8]``)) then
                                           concat [cmb1_name,":?u32","[",exp2ilexp_inner (comb_22),",  e_little]:u8"]
                                       else
                                           concat [cmb1_name,":?u32","[",exp2ilexp_inner (comb_22),",  e_little]:u32"]
				   else
				       concat [exp2ilexp_inner comb_11,
					       exp2ilexp_inner comb_22]
				end
			    else
				concat [exp2ilexp_inner comb_11,
					exp2ilexp_inner comb_22]
			end
		end
	    else "UNSUPPORTED"
    in 
	exp2ilexp_inner exp
    end;

fun exp2ilexp8 exp =
    let val dirty_exp_for_it_flag_thm = 
	    ``!x:bool[32].
		     (((15 >< 10) x) @@ ((26 >< 25) x)):bool[8] =
                     (n2w (w2n (
			   (((15 -- 10) x)) << 2 ‖
			   ((26 -- 25) x)
                      ))):bool[8]
            ``
	val _ = print_term dirty_exp_for_it_flag_thm
	val _ = print "TYPE\n"
	val _ = print_type (type_of exp)
	val exp = snd (dest_eq (concl (SIMP_RULE (srw_ss())
                      [ASSUME dirty_exp_for_it_flag_thm] (ASSUME
    ``ggg_xp=^exp``))))
	val _ = print "HELLO"
	val _ = print_term exp
    in

    if wordsSyntax.is_n2w exp then
       	let val (exp1, vtype) = wordsSyntax.dest_n2w exp in
	    (concat ["low:u8(",
		     (exp2ilexp64 exp1),
		     ")"])
	end
    else if is_var exp then
	let val (vname, vtype) = dest_var exp in
	    if type_of exp = ``:bool[8]`` then
		(concat [flag_st vname, ":u8"])
	    else
		(print "8: "; print_term exp; print " UNSUPPORTED\n";
		 "UNSUPPORTED")
	end
    else if (is_comb exp) then
	let val (comb_11,comb_22) = dest_comb exp
	in
	    if is_var comb_11 then
		let val (cmb1_name,_) = dest_var comb_11 in
		    if((type_of (comb_11) = ``:bool[32]->bool[8]``)) then
			concat [cmb1_name,":?u32","[",exp2ilexp32 (comb_22),",  e_little]:u8"]
		    else
			(print "8: "; print_term exp; print " UNSUPPORTED\n";
			 "UNSUPPORTED")
		end
	    else
		(print "8: "; print_term exp; print " UNSUPPORTED\n";
		 "UNSUPPORTED")
	end
    else
	(print "8: "; print_term exp; print " UNSUPPORTED\n";
	 "UNSUPPORTED")
    end

and exp2ilexp5 exp =
    if wordsSyntax.is_n2w exp then
       	let val (exp1, vtype) = wordsSyntax.dest_n2w exp in
	    (concat ["(0x1f:u8 & low:u8(",
		     (exp2ilexp64 exp1),
		     "))"])
	end
    else if is_var exp then
	let val (vname, vtype) = dest_var exp in
	    if type_of exp = ``:bool[5]`` then
		(concat ["(0x1f:u8 & ", flag_st vname, ":u8)"])
	    else
		(print "5: "; print_term exp; print " UNSUPPORTED\n";
		 "UNSUPPORTED")
	end
    else if (wordsSyntax.is_word_extract exp) then
	let val (ext_1,ext_2,ext_3,_) =  wordsSyntax.dest_word_extract exp in
	    concat [
	    "(0x1f:u8 & low:u8(",
	    "((",exp2ilexp ext_3 true, " & ", 
	    "((0x1:u32 << (low:u32(",exp2ilexp ext_1 true,")+1:u32))",
	    " - (0x1:u32 << (low:u32(",
	    exp2ilexp ext_2  true,
	    "))))) >> low:u32(",
	    exp2ilexp ext_2 true,"))))"]
	end
    else
	(print "5: "; print_term exp; print " UNSUPPORTED\n";
	 "UNSUPPORTED")

and exp2ilexp64 exp =
    if numSyntax.is_numeral exp then
	(concat 
	     ["0x" , (Int.fmt StringCvt.HEX (Arbnumcore.toInt(numSyntax.dest_numeral exp))),
	      ":u64"])
    else if numSyntax.is_plus exp then
	concat ["(",String.concatWith " + " (
		    map exp2ilexp64
			(numSyntax.strip_plus exp)),")"]
    else if wordsSyntax.is_w2n exp
	    (* andalso type_of exp = ``:bool[32]`` *)
    then
	(concat ["extend:u64","(",
		 (exp2ilexp32 (wordsSyntax.dest_w2n exp)),
		 ")"])
    else if (boolSyntax.is_cond exp) then
	let val (cond_1,cond_2,cond_3) = boolSyntax.dest_cond exp in
	    concat ["( if ",exp2ilexpbool cond_1," then ",exp2ilexp64 cond_2," else ", exp2ilexp64 cond_3,")" ]
	end
    else if (numSyntax.is_mod exp) then
	let val (mod_1,mod_2) = numSyntax.dest_mod exp in
	    concat ["(",exp2ilexp64 mod_1," % ",exp2ilexp64 mod_2,")"]
	end
    else
	(print "64: "; print_term exp; print " UNSUPPORTED\n";
	 "UNSUPPORTED")

and exp2ilexpbool exp =
(
    (print "LIFTING BOOL .. "; print_term exp; "\n");
    (* Bad stuff to do *)
    if  (is_lamb exp) then
 	exp2ilexpbool(dest_lamb exp)
    else if is_var exp then
	let val (vname, vtype) = dest_var exp in
	    if type_of exp = ``:bool`` then
		(concat [flag_st vname, ":bool"])
	    else
		(print "bool: "; print_term exp; print " UNSUPPORTED\n";
		 "UNSUPPORTED")
	end
    (* Extract bit k-th of n: (n & ( 1 << k )) >> k *)
    else if (wordsSyntax.is_index exp) then
	let val (index_1, index_2) = wordsSyntax.dest_index exp
	in
	    concat ["low:bool((", exp2ilexp32 index_1," & ",
		    "(0x1:u32 << (low:u32(",exp2ilexp64 index_2,
		    ")))) >> low:u32(", exp2ilexp64 index_2, "))"]
	end
    else if (is_neg exp) then
	let val neg_1 = dest_neg exp in
	    concat ["~",exp2ilexpbool neg_1]
	end
    else if wordsSyntax.is_word_1comp exp then
	(concat [" ~",(exp2ilexpbool (wordsSyntax.dest_word_1comp exp))])
    else if wordsSyntax.is_word_2comp exp then
	(concat [" -",(exp2ilexpbool (wordsSyntax.dest_word_2comp exp))])
    else if boolSyntax.is_conj exp then
	let val (conj_1, conj_2)= boolSyntax.dest_conj exp in
	    String.concatWith " & " [exp2ilexpbool conj_1, exp2ilexpbool conj_2]
	end
    else if boolSyntax.is_eq exp then
	let val (eq_1, eq_2) = boolSyntax.dest_eq exp in
	    concat ["(",String.concatWith " == "
					  [exp2ilexp eq_1 false,
					   exp2ilexp eq_2 false],")"]
	end
    else if (boolSyntax.is_disj exp) then
	let val (disj_1, disj_2) = boolSyntax.dest_disj exp in
	    concat ["(",exp2ilexp disj_1 false, "|", exp2ilexp disj_2 false, ")"]
	end
    else if (is_imp exp) then
    	let val (imp_1, imp_2) = dest_imp exp in
    	    concat ["(",String.concatWith " | " [concat ["~","(",(exp2ilexpbool imp_1),")"], exp2ilexpbool imp_2],")"]
    	end
    else if numSyntax.is_less exp then
	let val (ls_1, ls_2)= numSyntax.dest_less exp in 
	    String.concatWith " < " [exp2ilexp ls_1 false,
				     exp2ilexp ls_2 false]
	end
    else if wordsSyntax.is_word_lt exp then
	let val (ls_1, ls_2)= wordsSyntax.dest_word_lt exp in 
	    String.concatWith " < " [exp2ilexp ls_1 false,
				     exp2ilexp ls_2 false]
	end
    else if (wordsSyntax.is_word_le exp) then
	let val (le_1, le_2) = wordsSyntax.dest_word_le exp in
	    concat ["(",String.concatWith " $<= " [exp2ilexp le_1 false,
						  exp2ilexp le_2 false],")"]
	end 
    else if (wordsSyntax.is_word_ls exp) then
	let val (le_1, le_2) = wordsSyntax.dest_word_ls exp in
	    concat ["(",String.concatWith " <= " [exp2ilexp le_1 false,
						  exp2ilexp le_2 false],")"]
	end 
    else if (wordsSyntax.is_word_ge exp) then
	let val (ge_1, ge_2) = wordsSyntax.dest_word_ge exp in
	    concat ["(",String.concatWith " $>= " [exp2ilexp ge_1 false,
						  exp2ilexp ge_2 false],")"]
	end
    else if (wordsSyntax.is_word_hs exp) then
	let val (ge_1, ge_2) = wordsSyntax.dest_word_hs exp in
	    concat ["(",String.concatWith " >= " [exp2ilexp ge_1 false,
						  exp2ilexp ge_2 false],")"]
	end
    (*Bit theory page 85 : |- !b n. BIT b n = ((n DIV 2 ** b) MOD 2 = 1)*)
    else if (bitSyntax.is_bit exp) then
	let val (bit_1,bit_2) = bitSyntax.dest_bit exp
	    val _ = print "bit"
	in
	    concat["(((",exp2ilexp64 bit_2," / (","0x1:u64",
		   "<< ", exp2ilexp64 bit_1,"))"," % ",
		   "0x2:u64",")"," ==","0x1:u64",")"]
	end
    else if (wordsSyntax.is_word_msb exp) then
	let val mb_1 = wordsSyntax.dest_word_msb exp
	in if type_of mb_1 = ``:bool[32]`` then
		concat ["low:bool((",exp2ilexp32 mb_1,") >> 0x1f:u32 )"]
	    else
		concat ["low:bool((",exp2ilexp64 mb_1,") >> 0x1f:u64 )"]
	end
    else if (is_const exp) then
	let val (cnst_name,_) = dest_const exp 
	in
	    if (cnst_name = "F") then concat["false"]
	    else concat["true"]
	    
	end
    else if boolSyntax.is_disj exp then
	let val (disj_1, disj_2)= boolSyntax.dest_disj exp in
	    String.concatWith " & " [exp2ilexpbool disj_1, exp2ilexpbool disj_2]
	end
    else if (is_comb exp) then
	let val (comb_1,comb_2) = dest_comb exp
	    val (cst_name,_) = dest_const comb_1
	in
	    case cst_name of "aligned" => 
			     let val (_,comb_3) = strip_comb comb_2 in
				 concat ["(",exp2ilexp2 (hd comb_3)false," == ",exp2ilexp2 (hd(tl comb_3)) false,"*","(",exp2ilexp2 (hd comb_3) false,"$/",exp2ilexp2 (hd (tl comb_3)) false,"))"]
			     end
			   | "align" =>
			     let val (_,comb_3) = strip_comb comb_2 in
				 concat ["(",exp2ilexp2 (hd(tl comb_3))false,"*","(",exp2ilexp2 (hd comb_3) false,"$/",exp2ilexp2 (hd (tl comb_3)) false,"))"]
			     end
			   | "aligned_bx"=>
			     let val m = 1
				 val n = 0 in
				 concat ["((",exp2ilexp2 comb_2 false, " & ", "((0x1:u32 << ( ","0x",Int.fmt StringCvt.HEX m ,":u32","- 0x1:u32)) - (0x1:u32 << ( ","0x",Int.fmt StringCvt.HEX n,":u32","- 0x1:u32)))) >>","0x",Int.fmt StringCvt.HEX n,":u32",")"]
			     end
			   | "!" => 
			     let val (comb_11,comb_22) = strip_comb exp in
    	    	    		 concat [exp2ilexpbool (List.nth (comb_22,0))]
			     end
			   | _ => (print "bool: ";
				   print_term exp;
				   print " UNSUPPORTED\n";
				   "UNSUPPORTED")
	end
    else
	(print "bool: "; print_term exp; print " UNSUPPORTED\n";
	 "UNSUPPORTED")
)

and exp2ilexp32 exp =
    (print "LIFTING 32  "; print_term exp; print "\n";
    if is_var exp then
	let val (vname, vtype) = dest_var exp in
	    (concat [reg_st vname, ":u32"])
	end
    else if wordsSyntax.is_word_add exp then
	let val (exp1, exp2) = wordsSyntax.dest_word_add exp in
	    concat ["(",String.concatWith " + " [exp2ilexp32 exp1 , exp2ilexp32 exp2],")"]
	end
    else if (wordsSyntax.is_word_or exp) then
	let val (or_1,or_2) = wordsSyntax.dest_word_or exp in
	    String.concatWith " | " [exp2ilexp32 or_1, exp2ilexp32 or_2]
	end
    else if wordsSyntax.is_word_1comp exp then
	(concat [" ~",(exp2ilexp32 (wordsSyntax.dest_word_1comp exp))])
    else if wordsSyntax.is_word_2comp exp then
	(concat [" -",(exp2ilexp32 (wordsSyntax.dest_word_2comp exp))])
    else if wordsSyntax.is_word_and exp then
      	let val (exp1,exp2) = wordsSyntax.dest_word_and exp in
	    concat ["(",String.concatWith " & " [exp2ilexp32 exp1 , exp2ilexp32 exp2],")"]
	end
    else if (wordsSyntax.is_word_lsl exp) then
	let val (lsl_1, lsl_2) = wordsSyntax.dest_word_lsl exp in
	    concat ["(", String.concatWith " << " [exp2ilexp32 lsl_1,
						   (concat ["low:u32(",
							    (exp2ilexp64 lsl_2),
							    ")"])
						  ],")"]
	end
    else if (wordsSyntax.is_word_lsr exp) then
	let val (lsl_1, lsl_2) = wordsSyntax.dest_word_lsr exp in
	    concat ["(",String.concatWith " >> " [exp2ilexp32 lsl_1,
						  (concat ["low:u32(",
							   (exp2ilexp64 lsl_2),
							   ")"])
						 ],")"]
	end
    else if (wordsSyntax.is_word_asr exp) then
	let val (lsl_1, lsl_2) = wordsSyntax.dest_word_asr exp in
	    concat ["(",String.concatWith " $>> " [exp2ilexp32 lsl_1,
						   (concat ["low:u32(",
							    (exp2ilexp64 lsl_2),
							    ")"])
						  ],")"]
	end
    else if (wordsSyntax.is_word_xor exp) then
	let val (xor_1,xor_2) = wordsSyntax.dest_word_xor exp in
	    concat ["(", exp2ilexp32 xor_1,"^", exp2ilexp32 xor_2,")"]
	end
    else if (wordsSyntax.is_word_mul exp) then
	let val (mul_1,mul_2) = wordsSyntax.dest_word_mul exp in
	    concat ["(", exp2ilexp32 mul_1,"*", exp2ilexp32 mul_2,")"]
	end
    else if (numSyntax.is_mod exp) then
	let val (mod_1,mod_2) = numSyntax.dest_mod exp in
	    concat ["(",exp2ilexp32 mod_1," % ",exp2ilexp32 mod_2,")"]
	end
    else if (boolSyntax.is_cond exp) then
	let val (cond_1,cond_2,cond_3) = boolSyntax.dest_cond exp in
	    concat ["( if ",exp2ilexpbool cond_1," then ",exp2ilexp32 cond_2," else ", exp2ilexp32 cond_3,")" ]
	end
    else if wordsSyntax.is_n2w exp then
       	let val (exp1, vtype) = wordsSyntax.dest_n2w exp in
	    (concat ["low:u32(",
		     (exp2ilexp64 exp1),
		     ")"])
	end
    else if numSyntax.is_numeral exp then
	(concat
	     ["0x" , (Int.fmt StringCvt.HEX (Arbnumcore.toInt(numSyntax.dest_numeral exp))),
	      ":u32"])
    else if (wordsSyntax.is_word_bits exp) then
	let val (bts_1,bts_2,bts_3) =  wordsSyntax.dest_word_bits exp 
	    val num_e2 = Arbnumcore.toInt(numSyntax.dest_numeral bts_2)
	in
	    if (num_e2 = 0) then
		concat ["(",exp2ilexp32 bts_3, " & ", "(low:u32(","0xFFFFFFFF:u32"," << ",exp2ilexp32 bts_1,"))",")"]
	    else
		concat ["((",exp2ilexp32 bts_3 , " & ", 
			"((0x1:u32 << (",exp2ilexp32 bts_1 ,"- 0x1:u32)) - (0x1:u32 << (",exp2ilexp32 bts_2,"- 0x1:u32)))) >>",exp2ilexp32 bts_2,")"]
	end
    else if (is_comb exp) then
	let val (comb_1,comb_2) = dest_comb exp in
	    if (is_const comb_1) then
		let val (cst_name,_) = dest_const comb_1 in
		    case cst_name of "align" =>
				     let val (_,comb_3) = strip_comb comb_2 in
					 concat ["((low:u32(",exp2ilexp64 (hd(tl comb_3)),")*",exp2ilexp32 (hd comb_3),")$/low:u32(",exp2ilexp64 (hd (tl comb_3)),"))"]
				     end
				   | "LSR_C" => 
				     let val (_,comb_3) = strip_comb comb_2 in
					 concat["(((",exp2ilexp32 ( hd comb_3)," / ( ","0x2:u32"," << ","(", exp2ilexp32 (hd (tl comb_3)),"- 0x1:u32 )))","%","0x2:u32",")"," == ","0x1:u32",")"]
				     end
				   |_ => 
				    (print "32: "; print_term exp;
				     print " UNSUPPORTED const"; print cst_name; print "\n";
				     "UNSUPPORTED")

		end
	    else if (is_var comb_1) then
		let val (cmb1_name,_) = dest_var comb_1
		    val ext_bool_flag = (
			fn (flag, bits) =>
			   concat [
			   "((extend:u32(",
			   exp2ilexpbool (my_eval flag),
			   ") << ", bits, ":u32)",
			   "& (0x1:u32 << ",
			   bits, ":u32))"])
		in if cmb1_name = "guancio_psr_to_reg" then
		       concat [
		       "(",
		       ext_bool_flag (``^comb_2.N``, "31"), "|", 
		       ext_bool_flag (``^comb_2.Z``, "30"), "|", 
		       ext_bool_flag (``^comb_2.C``, "29"), "|", 
		       ext_bool_flag (``^comb_2.V``, "28"), "|", 
		       ext_bool_flag (``^comb_2.Q``, "27"), "|", 
		       ext_bool_flag (``^comb_2.J``, "24"), "|", 
		       ext_bool_flag (``^comb_2.E``, "9"), "|", 
		       ext_bool_flag (``^comb_2.A``, "8"), "|", 
		       ext_bool_flag (``^comb_2.I``, "7"), "|", 
		       ext_bool_flag (``^comb_2.F``, "6"), "|", 
		       ext_bool_flag (``^comb_2.T``, "5"), "|",
		       "pad:u32(", exp2ilexp (my_eval ``^comb_2.M``) true,")",
		       ")"
		       ]
		   else
		       concat [exp2ilexp32 comb_1,
			       exp2ilexp32 comb_2]
		end
	    else
		let val (exc_1, exc_2) = strip_comb exp
		in if(is_const exc_1) then
		       let val (cst_name,_) = dest_const exc_1 in
			   case cst_name of
			       "read_mem32" => 
			       let val (mm_str,mm_type) = dest_var (List.nth(exc_2,1))
			       in
				   concat [mm_str,":?u32","[",exp2ilexp32 (List.nth (exc_2,0)),",  e_little]:u32"]
	                       end
			     |_ => (print "32: ";
				    print_term exp;
				    print " UNSUPPORTED comb\n";
				    "UNSUPPORTED")
		       end
		   else
		       (print "32: ";
			print_term exp;
			print " UNSUPPORTED comb\n";
			"UNSUPPORTED")
		end
	end
    else
	(print "32: "; print_term exp; print " UNSUPPORTED\n";
	 "UNSUPPORTED")
)

and exp2ilexp exp extend =
    let val exp = snd (dest_eq (concl (
		SIMP_RULE (srw_ss()) [] (ASSUME ``ggg_xp=^exp``))))
    in
	(print "LIFTING.. "; print_term exp; print_type (type_of exp); print "\n";
	 if type_of exp = ``:bool[32]`` then
	     exp2ilexp32 exp
	 else if type_of exp = ``:bool[64]`` then
	     exp2ilexp64 exp
	 else if type_of exp = ``:bool`` then
	 exp2ilexpbool exp
	 else if type_of exp = ``:bool[8]`` then
	     exp2ilexp8 exp
	 else if type_of exp = ``:bool[5]`` then
	     exp2ilexp5 exp
	 else
	     exp2ilexp64 exp
	)
    end;

fun reg_changed state dest_reg = 
    let val reg_value = read_reg state dest_reg
    in
	if is_var reg_value then
       	    let val (vname, vtype) = dest_var reg_value in
		not (vname = dest_reg)
	    end
	else
	    true
    end;

fun lift_single_reg_effects state dest_reg = 
    let val reg_value = read_reg state dest_reg
	val reg_il = exp2ilexp reg_value false
    in
	concat ["tmp_",dest_reg,":u32 = ", reg_il, "\n"]
    end

fun mem_rd_worker accesses =
    let val (acc_1, acc_2) = listSyntax.dest_list accesses
	val acc_ls_1 = trimer_ls acc_1 0 4
	val itr = div ((List.length (acc_ls_1)),4)
	fun ls_div fls lo up  =
	    if (up < 0) then
		fls
	    else
		let val acc_el_1 = trimer_ls acc_ls_1 lo up
		    val (_,acc_el_2) = strip_comb (last acc_el_1) 
		in
		    ls_div (fls@acc_el_2) (lo+4) (up-4)
		end
    in
	ls_div [] 0 ((itr-1)*4)
    end;


fun lift_reg_memory_read state regs =
    let 
	val ls = filter (reg_changed state) std_reg_list
	val accesses = read_accesses state
	val (acc_1, acc_2) = listSyntax.dest_list accesses
	val acc_ls = trimer_ls acc_1 0 4
	val exps = mem_rd_worker accesses
    in
	case List.null ls of false => 
			     let 
				 val creg = read_reg state (hd (ls))
			     in
				 if (wordsSyntax.is_w2w creg ) then
				     let val (wreg,_) = wordsSyntax.dest_w2w creg
				     in
					 if (not(wordsSyntax.is_word_concat wreg ))
					 then
					     let 
						 val (_,acc_el) = strip_comb ((hd acc_ls))
					     in
						 [concat [(hd ls),":u32 = pad:u32(mem:?u32[", exp2ilexp (hd acc_el) false," ,e_little]:u8)\n"]]
					     end
					 else
					     let 
						 val (_,acc_el) = strip_comb ((hd (tl acc_ls)))
					     in
						 [concat [(hd ls),":u32 = pad:u32(mem:?32[", exp2ilexp (hd acc_el) false," ,e_little]:u16)\n"]]
					     end
				     end
				 else
				    (map (fn (exp, reg) =>
					     concat ["tmp_", reg, ":u32 = mem:?u32[", exp2ilexp exp false, ",e_little]:u32\n"])
					 (ListPair.zip(exps, List.rev regs)))
			     end
			   | true =>
				  (map (fn (exp, reg) =>
					 concat ["tmp_", reg, ":u32 = mem:?u32[", exp2ilexp exp false, ",e_little]:u32\n"])
				 (ListPair.zip(exps, List.rev regs)))
    end;


fun lift_reg_effects state =
    let
	val updated_regs = filter (reg_changed state) std_reg_list

    in
	if(List.null(filter (reg_changed state) ["pc"])) then
	   let val updated_regs_mem = filter (
				   fn reg_name =>
				      let 
					  val reg_value = read_reg state reg_name
				      in (wordsSyntax.is_word_concat reg_value orelse wordsSyntax.is_w2w reg_value orelse is_cond reg_value)
				      end
				   ) updated_regs
	       val updated_regs_standard = filter (
					   fn reg_name =>
					      not (member reg_name updated_regs_mem)
					   ) updated_regs;
	   in
	       (
		(List.map (lift_single_reg_effects state) updated_regs_standard)
		@
		(lift_reg_memory_read state updated_regs_mem),
		List.map 
		    (fn dest_reg =>
	    		concat [reg_st dest_reg,":u32 = ", "tmp_", dest_reg, ":u32\n"]
		    )
		    updated_regs
	       )
	   end
	 else
	   let val updated_regs_mem = filter (
				   fn reg_name =>
				      let 
					  val reg_value = read_reg state reg_name
				      in (wordsSyntax.is_word_concat reg_value orelse wordsSyntax.is_w2w reg_value orelse is_cond reg_value)
				      end
				   ) (updated_regs@["pc"])
	       val updated_regs_standard = filter (
					   fn reg_name =>
					      not (member reg_name updated_regs_mem)
					   ) updated_regs
	   in
	       (
		(List.map (lift_single_reg_effects state) updated_regs_standard)
		@
		(lift_reg_memory_read state updated_regs_mem),
		List.map 
		    (fn dest_reg =>
	    		concat [reg_st dest_reg,":u32 = ", "tmp_", dest_reg, ":u32\n"]
		    )
		    updated_regs
	       )
	   end
    end;

(* write memory *) 
fun mem_wr_worker accesses =
    let val itr = div ((List.length (accesses)),4)
	fun ls_div fls lo up  =
	    if (up < 0) then
		fls
	    else
		let val acc_el_1 = trimer_ls accesses lo up
		    val (_,acc_el_2) = strip_comb (last acc_el_1)
		    val acc_el_3 = hd acc_el_2
		    val (_,acc_el_4) = (dest_comb (last acc_el_2))
		in
		    ls_div (fls@[(acc_el_3, acc_el_4)]) (lo+4) (up-4)
		end
    in
	ls_div [] 0 ((itr-1)*4)
    end;

fun lift_mem_write state =
    let val accesses = read_accesses state
	val (mlAccesses, listType) = listSyntax.dest_list accesses
	val wr_accesses = filter (
			  fn (acc) =>
			     let val (comb_1,comb_2) = strip_comb acc
				 val (cst_name,_) = dest_const comb_1
			     in
				 cst_name = "MEM_WRITE"
			     end
			  ) mlAccesses
	    val mem_wrs = mem_wr_worker wr_accesses
    in
	if(List.null mem_wrs andalso not (List.null wr_accesses)) then
	    let val (_,ctmp) = dest_comb (hd wr_accesses)
	    in
		if (wordsSyntax.is_w2w ctmp) then
		    let val (tmp1,tmp2) = dest_comb(hd wr_accesses)
			val (_,tmp3) = dest_comb tmp1
			val (tmp4,_) = wordsSyntax.dest_w2w tmp2
		    in
			[concat ["mem:?u32 = mem:?u32 with [",
				 exp2ilexp tmp3 false,
				 " ,e_little]:u8 = (low:u8(",
				 exp2ilexp tmp4 false,"))" ]]
		    end
		else
		    let val (tmp1,tmp2) = dest_comb(hd (tl wr_accesses))
			val (_, tmp3) = dest_comb tmp1
			val (_, tmp4) = dest_comb tmp2
		    in
			[concat ["mem:?u32 = mem:?u32 with [",
				 exp2ilexp tmp3 false,
				 " ,e_little]:u16 = (low:u16(",
				 exp2ilexp tmp4 false,"))" ]]
		    end
	    end
	 else
	    map (fn (add, exp) =>
		    concat ["mem:?u32 = mem:?u32 with [",
			    exp2ilexp add false,
			    " ,e_little]:u32 =",
			    exp2ilexp exp false,"\n" ]
		) mem_wrs
    end;
(* end memory management *)

(* TODO: All filter shoud be done not on variable name but *)
(* comparing expression in previous and next state *)
fun flag_changed old_psr psr var_prefix dest_flag = 
    let val old_flag_value = read_flag old_psr dest_flag
	val flag_value = read_flag psr dest_flag
    in
	flag_value <> old_flag_value
    end;

fun gen_bap_type_var_for_value value =
    if (type_of value) = ``:bool`` then
	"bool"
    else if (type_of value) = ``:bool[5]`` then
	"u8"
    else "u32";
	
fun lift_flag_effects_single_psr old_state state (psr, var_prefix) =
    let 
	val cpsr = read_psr state  psr
	val old_cpsr = read_psr old_state  psr
	val updated_flags = filter (flag_changed old_cpsr cpsr var_prefix) std_flag_list

    in
	(
	 List.map 
	     (fn dest_flag =>
	    	 let
		     val flag_value = read_flag cpsr  dest_flag 
		     val flag_type = gen_bap_type_var_for_value flag_value
	    	     val flag_il = exp2ilexp flag_value true
	    	 in
		     if String.isSubstring "UNSUPPORTED" flag_il then
	    		 concat
			     ["tmp_",var_prefix,dest_flag,":",
			      flag_type," = ",
			      flag_st (concat [var_prefix, dest_flag]),
			      ":",flag_type, "\n"]
		     else
	    		 concat
			     ["tmp_",var_prefix,dest_flag,":",
			      flag_type," = low:",flag_type,"(", flag_il, ")\n"]
			 
	    	 end
	     )
	     updated_flags
	     ,
	 List.map 
	     (fn dest_flag =>
		 let val flag_value = read_flag cpsr  dest_flag 
		     val flag_type = gen_bap_type_var_for_value
					 flag_value
		 in
	    	     concat [flag_st (concat [var_prefix, dest_flag]),
			 ":",flag_type," = ", "tmp_",var_prefix,
	dest_flag, ":",flag_type,"\n"]
		 end
	     )
	     updated_flags
	)
    end;

fun lift_flag_effects old_state state =
    List.foldl
    	(fn ((eff_a1, eff_a2), (eff_b1, eff_b2)) =>
    	    (List.concat [eff_a1, eff_b1],
	     List.concat [eff_a2, eff_b2])
    	)
    	([], [])
        (List.map (lift_flag_effects_single_psr old_state state) [
             (``CPSR``, ""),
    	     (``SPSR_svc``, "svc_")
        ]);

fun lift_side_effects old_state state =
    let val (reg_up1, reg_up2) = lift_reg_effects state
	val (flag_up1, flag_up2) = lift_flag_effects old_state state
	val mem_up1 = lift_mem_write state
    in
	concat [concat reg_up1,
		concat flag_up1,
		concat mem_up1,
		concat reg_up2,
		concat flag_up2
	       ]
    end;


