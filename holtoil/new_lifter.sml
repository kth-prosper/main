load "armLib";
load "arm_evalLib";
load "arm_seq_monadTheory";
load "stringLib";

use "holtoil/new_lifter_exp.sml";

(*===============================Global Variables ================================*)
val working_directory = ref "";
val var_index = ref 0;
val label_index = ref 0;
val cmd_cntr = ref 0;


fun get_il_file_name () = (concat [(* !working_directory, *) "../arm_to_ir.il"])

val hex = Int.fmt StringCvt.HEX;

fun objdump infile outfile =
    let val _ = OS.FileSys.access (infile, [OS.FileSys.A_READ]) orelse
                raise OS.SysErr ("Cannot read file: " ^ infile,NONE)
        val s = String.concat ["arm-elf-objdump -d -j .text -j .data -j .rodata ",
                               infile, " > ", outfile]
        val _ = OS.Process.isSuccess (OS.Process.system s) orelse
                raise OS.SysErr ("Failed to run arm-elf-objdump",NONE)
    in
        ()
    end;

fun parse_objdump infile =
    let val istrm = TextIO.openIn infile
        val inp = TextIO.inputAll istrm before TextIO.closeIn istrm
        val l = List.drop (String.tokens (fn c => c = #"\n") inp, 3)
        fun get_tokens s =
            case String.tokens (fn c => c = #":") s
             of (n::instr::rest) =>
                (n, remove_padding
                        (hd (String.tokens (fn c => c = #"\t") instr)))
              | _ => raise ERR "parse_objdump" "failed to parse line"
    in
        Lib.mapfilter get_tokens l
    end;
fun load_elf infile =
    let val tmp = OS.FileSys.tmpName ()
        val _ = objdump infile tmp
    in
        parse_objdump tmp before OS.FileSys.remove tmp
    end;
(*===============================elf file loader end ==============================*)

(* il generation *)
fun inc selc =
    case selc of "var" =>
		 var_index := !var_index + 1
	       |"label" =>
		label_index := !label_index + 1
	       | "cmd" =>
		 cmd_cntr  := !cmd_cntr + 4
	       |_ =>  raise ERR "inc" "Not supported experssion";
fun tmp_var_gen var_type =
    let val _ = inc "var"
	val t_index = Lib.int_to_string (!var_index) 
    in   
	case var_type of "w" =>	    
			 String.concat ["TmpV_", t_index,":u32"]
		       |"h" =>
			String.concat ["TmpV_", t_index,":u16"]
		       |"bt" =>
			String.concat ["TmpV_", t_index,":u8"]
		       |"b" =>
			String.concat ["TmpV_", t_index,":bool"]
		       |"ex" =>
			String.concat ["TmpV_", t_index,":u64"]
		       |_ => ""
    end;
fun tmp_label_gen () =
    let val _ = inc "label"
	val t_index = Lib.int_to_string (!label_index) 
	val tmp_label = String.concat ["L_", t_index]
    in
	tmp_label
    end;

(*=============================== write file ===============================*)

fun append_to_file text =
    let	val fhdl = TextIO.openAppend (get_il_file_name())
    in
	(TextIO.output (fhdl, text);
	 TextIO.closeOut fhdl)
    end

fun write_to_file ls command =
    let	val fhdl = TextIO.openAppend (get_il_file_name())
	val () = TextIO.output (fhdl, (concat["\n","addr ","0x", hex (!cmd_cntr), " @asm  ", "\"",command,"\"","\n"]))
	val () = TextIO.output (fhdl, (concat["label ","pc_","0x" , hex (!cmd_cntr),"\n"]))
	val () = inc "cmd"
	fun helper lls =
	    case List.null lls of true => (TextIO.closeOut fhdl)
				| false => ( TextIO.output (fhdl, (hd lls)); helper (tl lls))
    in

	helper ls
    end
(*=============================== write file-end============================*)
(*=============================== read file ================================*)
fun read_file (infile : string) =
    let 
	fun str_trimer exp =
	    let val str_len = String.size exp
	    in
		String.substring (exp, 0, (str_len -1 ))
	    end    
	fun readlist (infile : string) = let
	    val ins = TextIO.openIn infile
	    fun loop ins =
		case TextIO.inputLine ins of
		    SOME line => line :: loop ins
		  | NONE      => []
	in
	    map str_trimer (loop ins before TextIO.closeIn ins)
    	end 
    	fun machine_code_ex str =
    	    let val (_, suf) =Substring.splitl (fn ch => ch <> #"\t") (Substring.full str)
    	    in
    		String.substring ((String.substring ((Substring.string suf), 1, 9)),0,8)
		       handle Subscript => ""
    	    end
    in
    	filter (fn str => String.size str > 0 ) (map machine_code_ex (readlist infile))
    end;
(*=============================== read file-end============================*)

fun state_from_rule rule_th = 
    if (isSome rule_th) then
	let val (exp_pre, exp_post) = step_th_to_exprs (valOf rule_th)
	    (* Remove the problem of monitors in symbolic mode *)
	    val t = ASSUME ``!a. CLEAR_EXCLUSIVE_BY_ADDRESS a = \b.b``
	    val new_th = REWRITE_RULE [t] (ASSUME ``
				      new_state = ^exp_post``)
	    val (_, new_concl) = dest_thm new_th
	    val (_, exp_post) = dest_eq new_concl
	    (* End of fix for the problem of monitors in symbolic mode *)
	    (* Remove the problem of encode psr in symbolic mode *)
	    val t = ASSUME ``!p. encode_psr p = guancio_psr_to_reg(p)``
	    val new_th = REWRITE_RULE [t] (ASSUME ``
				      new_state = ^exp_post``)
	    val (_, new_concl) = dest_thm new_th
	    val (_, exp_post) = dest_eq new_concl
	    (* End of fix for the problem of of encode psr in symbolic mode *)
	    val state = build_sym_state()
	    val next_state = apply_exp_to_state exp_post state
	    val pre_condition = apply_exp_to_state exp_pre state
	in SOME (
	   pre_condition, next_state
	   )
	end
    else NONE;


fun states_from_instruction code = 
    let val steps = armLib.arm_steps_from_string "svc,little-endian,arm" code (*"usr,big-endian,arm" code*)
    (* let val steps = armLib.arm_steps_from_string "usr,little-endian,arm" code *)
	val (step_if, step_else) = hd steps
	val step_if = SOME step_if
	val if_branch = state_from_rule step_if
	val else_branch = state_from_rule step_else
    in
	if (isSome else_branch) then [valOf if_branch, valOf else_branch]
	else [valOf if_branch]
    end;
	

fun pc_frm exp state typ =
    let 
	val pc_pre = !cmd_cntr
	val pc_term = numSyntax.term_of_int pc_pre
	val pc_num = my_eval ``let pc=((n2w(^pc_term)):bool[32]) in
				   w2n ^exp``
	val pc_num = snd (dest_eq (concl (SIMP_RULE (srw_ss())
                                       [ASSUME ``~((lr_svc:bool[32]) ' 0)``]
				       (ASSUME ``a = ^pc_num``))))

    in 
	if(typ = "s") then
	    if numSyntax.is_numeral pc_num then
		let val pc_val = Arbnumcore.toInt(
	    			 numSyntax.dest_numeral pc_num)
		in
	    	    if  (pc_val < 4294967296) then
    	    		concat["\"","pc_","0x" ,hex (pc_val) ,"\""]
    	    	    else
    	    		concat["\"","pc_","0x" ,hex (mod ((pc_val - 1), 4294967295) ) ,"\""]
    		end
	    else
		let 
		    val tmpv = wordsSyntax.dest_w2n pc_num
		in
		    if(is_cond tmpv) then
			let 
			    val (cond_1,_,_) = boolSyntax.dest_cond tmpv
			    val (index_1, _) = wordsSyntax.dest_index cond_1
			in
			    if(is_var index_1)  then
				exp2ilexp32 tmpv
			    else
				let val str =hd (lift_reg_memory_read state ["pc"])          in 
				    concat[String.substring (str,12, String.size(str)-12)]  end
			end
		    else
			exp2ilexp32 tmpv
		end
	else if (typ = "n") then
	    if numSyntax.is_numeral pc_num then
		let val pc_val = Arbnumcore.toInt(
	    			 numSyntax.dest_numeral pc_num)
		in
	    	    if  (pc_val < 4294967296) then
    	    		concat["0x",hex (pc_val),":u32"]
    	    	    else
    	    		concat["0x",hex (mod ((pc_val - 1), 4294967295) ),":u32"]
    		end
	    else
		let 
		    val tmpv = wordsSyntax.dest_w2n pc_num
		in
		    if(is_cond tmpv) then
			let val str =hd (lift_reg_memory_read state ["pc"])          in 
			    concat[String.substring (str,12, String.size(str)-12)]  end
		    else
			exp2ilexp32 tmpv
		end
	else
	    raise ERR "pc_frm" "failed to parse line"
    end;
	
fun lift_instruction_inner machine_code =
    let val command = armLib.arm_disassemble_decode machine_code
	val old_state = build_sym_state()
	val states = states_from_instruction command
	val (cond, state_if) = hd states
	val cond = remove_e1_flag_from_condition (remove_align_from_condition cond)
	val pc_if = read_reg state_if "pc"
	val state_if_side_effects = lift_side_effects old_state state_if
	val pc_val = concat [reg_st "pc",":u32 = ", "0x" ,hex (!cmd_cntr),":u32"]
    in
	(* if (cond = ``T``) then *)
	if (List.length states = 1) then
	    (if(String.size state_if_side_effects = 0) then
		  let 
		      val j_pc_if =  pc_frm pc_if state_if "s" in
		  (write_to_file [concat [pc_val,"\n",
					  "PC:u32 = ", (pc_frm pc_if state_if "n"),"\n",
					 "jmp  ",j_pc_if, "\n",
					 ""
				]] command; [ j_pc_if])
		  end
	      else
		  let val j_pc_if =  pc_frm pc_if state_if "s";
		  in
		      if(List.null(filter (reg_changed state_if) ["pc"])) then 
			  ( write_to_file [concat [pc_val,"\n",
						   state_if_side_effects,
						   "PC:u32 = ",(pc_frm pc_if state_if "n"
								handle Empty =>
								       j_pc_if),"\n",
						   "jmp  ", j_pc_if, "\n",
						   ""
					  ]] command; [ j_pc_if])
		      else
			  if(is_cond pc_if) then
				let val (cond_1,_,_) = dest_cond pc_if 
				    val (index_1, _) = wordsSyntax.dest_index cond_1 in
				    if(wordsSyntax.is_word_concat index_1) then
		  			( write_to_file [concat [pc_val,"\n",
		  						 state_if_side_effects,
								 "PC:u32"," = ", "tmp_pc:u32","\n",
		  						 "jmp  ","PC:u32", "\n",
		  						 ""
		  					]] command; [ j_pc_if])
				    else
					( write_to_file [concat [pc_val,"\n",
								 state_if_side_effects,
								 "PC:u32 = ",(pc_frm pc_if state_if "n"
									      handle Empty =>
										     j_pc_if),"\n",
								 "jmp  ", j_pc_if, "\n",
								 ""
							]] command; [ j_pc_if])
				end
			  else
			      ( write_to_file [concat [pc_val,"\n",
						       state_if_side_effects,
						       "PC:u32 = ",(pc_frm pc_if state_if "n"
								    handle Empty =>
									   j_pc_if),"\n",
						       "jmp  ", j_pc_if, "\n",
						       ""
					      ]] command; [ j_pc_if])
		  end
	     )
	else
	    let	val cond_var_1 = tmp_var_gen "b"
		val label_if = tmp_label_gen ()
		val label_else = tmp_label_gen ()
		val ilcond = exp2ilexp cond false
		val (_, state_else) = hd (tl states)
		val pc_else = read_reg state_else "pc"
		val state_if_side_effects = lift_side_effects
						old_state state_if
		val state_else_side_effects = lift_side_effects
						  old_state state_else
	    in
		((
		 if (String.size state_if_side_effects = 0 andalso String.size state_else_side_effects = 0 ) then
		     let val j_pc_if =  pc_frm pc_if state_if "s"
			 val j_pc_else = pc_frm pc_else state_if "s"
		     in
		     (write_to_file [concat [ pc_val,"\n",
					     cond_var_1," = ","low:bool","(",ilcond,")","\n",
					     "cjmp ", cond_var_1, " , ", j_pc_if," , ", j_pc_else,"\n",
					     ""]] command;[j_pc_if, j_pc_else])
		     end
		 else if (String.size state_if_side_effects = 0 ) then
		     let val j_pc_if =  pc_frm pc_if state_if "s"
			 val j_pc_else = pc_frm pc_else state_if "s"
		     in
		    ( write_to_file [concat [ pc_val,"\n",
					     cond_var_1," = ","low:bool","(",ilcond,")","\n",
					     "cjmp ", cond_var_1, " , ", j_pc_if," , ","\"",label_else,"\"","\n",
					     "label ",label_else,"\n",
					     state_else_side_effects,
					      "PC:u32 = ",(pc_frm pc_else state_if "n") ,"\n",
					     "jmp  ", j_pc_else, "\n",
					     ""]] command;[j_pc_if, j_pc_else])
		     end
		 else if (String.size state_else_side_effects = 0 ) then
		     let val j_pc_if =  pc_frm pc_if state_if "s"
			 val j_pc_else = pc_frm pc_else state_if "s"
		     in
		     (write_to_file [concat [ pc_val,"\n",
					     cond_var_1," = ","low:bool","(",ilcond,")","\n",
					     "cjmp ", cond_var_1, " , ","\"", label_if,"\""," , ",j_pc_else,"\n",
					     "label ",label_if,"\n",
					     state_if_side_effects,
					      "PC:u32 = ",(pc_frm pc_if state_if "n"),"\n",
					     "jmp  ", j_pc_if, "\n",
					     ""
				   ]] command;[j_pc_if, j_pc_else])
		     end
		 else
		     let val j_pc_if =  pc_frm pc_if state_if "s"
			 val j_pc_else = pc_frm pc_else state_if "s"
		     in
		     (write_to_file [concat [ pc_val,"\n",
					     cond_var_1," = ","low:bool","(",ilcond,")","\n",
					     "cjmp ", cond_var_1, " , ","\"", label_if,"\""," , ","\"",label_else,"\"","\n",
					     "label ",label_if,"\n",
					     state_if_side_effects,
					      "PC:u32 = ",(pc_frm pc_if state_if "n"),"\n",
					     "jmp  ", j_pc_if, "\n",
					     "label ",label_else,"\n",
					     state_else_side_effects,
					      "PC:u32 = ",(pc_frm pc_else state_if "n"),"\n",
					     "jmp  ", j_pc_else, "\n",
					     ""
				   ]] command;[j_pc_if, j_pc_else])
		     end
		 ))
	    end
    end;

fun lift_instruction machine_code =
    (print (concat [hex (!cmd_cntr), "\n"]);
     lift_instruction_inner  machine_code
     handle Undefined => 
	    let val command = armLib.arm_disassemble_decode machine_code
	    in
		((write_to_file ["\n//Failed to lift\n",
			       "jmp \"lift_error\"\n"]
			      command);[])
	    end
    );

