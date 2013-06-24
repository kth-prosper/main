(* ============================================================================= *)

use "holtoil/new_lifter_exp.sml";

fun write_to_file ls =
    "ERROR";


fun post_lifter exp =
    [exp2ilexp exp false]
    (* if(is_eq exp ) then *)
    (* 	let *)
    (* 	    val (eq_1, eq_2) = boolSyntax.dest_eq exp *)
    (* 	in *)
    (* 	    if (wordsSyntax.is_word_concat eq_1) then *)
    (* 		let *)
    (* 		    val (cnct_1,cnct_2) = wordsSyntax.dest_word_concat eq_1 *)
    (* 		    val cnct_t1 = exp2ilexp2 cnct_1 false *)
    (* 		    val cnct_t2 = exp2ilexp2 cnct_2 false *)
    (* 		in *)
    (* 		    (* (!a b c. *) *)
    (* 		    (* 	((a:word6) @@ (b:word2) = c) = (a = (7 >< 2) c) /\ (b = (1 >< 0) c))`, *) *)
    (* 		   [concat ["((",cnct_t1,")"," == ", *)
    (* 			     "((",exp2ilexp2 eq_2 false , " & ", "((0x1:u32 << ("," 0x6:u32)) - (0x1:u32 << ("," 0x1:u32)))) >>","0x2:u32","))","&", *)
    (* 			     "((",cnct_t2,")"," == ", *)
    (* 			     "((",exp2ilexp2 eq_2 false , " & ", "0x00000003:u32",")))"]] *)
    (* 		end *)
    (* 	    else if (is_comb eq_1) then *)
    (* 		let val (comb_1,comb_2) = strip_comb eq_1 *)
    (* 		in *)
    (* 		    if (is_const comb_1) then *)
    (* 			let val (cst_name,_) = dest_const comb_1 *)
    (* 	    		in *)
    (* 	    		    case cst_name of "RName_User_case" => *)
    (* 					     let val ls_1 = (map (fn el => exp2ilexp2 el false) comb_2) *)
    (* 				       		 val (_,comb_3) = strip_comb eq_2 *)
    (* 				       		 val ls_2 = (map (fn el => exp2ilexp2 el false) comb_3) *)
    (* 				       	     in *)
    (* 				       		ListPair.map (fn (el_1,el_2) => concat [el_1, " == ", el_2," & \n"])(ls_1, ls_2) *)
    (* 				       	     end *)
    (* 					   |_=> [exp2ilexp2 exp false] *)
						
    (* 	    		end *)
    (* 		    else [exp2ilexp2 exp false] *)
    (* 		end *)
    (* 	    else [exp2ilexp2 exp false] *)
    (* 	end *)
    (* else [exp2ilexp2 exp false]; *)




fun convert_to_bap_condition cnd =
    let val cn_el = strip_conj cnd
	val cnd_lst_lst = map post_lifter cn_el
	val cnd_lst_lst = map (filter (
			       fn x => not (
				       String.isSubstring "UNSUPPORTED" x)))
			      cnd_lst_lst
	val cnd_lst = map (String.concatWith " & \n") cnd_lst_lst
	val cnd_lst = filter (fn x => size x > 0)
			      cnd_lst
	val cnd_str = String.concatWith " & \n" cnd_lst
    in
	cnd_str
    end;

fun save_bap_condition cnd file_name =
    let val fd = TextIO.openOut file_name
    in
	(TextIO.output (fd, cnd);
	 TextIO.closeOut fd)
    end;


(* fun gen_send_message_post () = *)
(*     let val hol_post = send_hol_postcondition() *)
(* 	val hol_post = simpl_transformation hol_post *)
(* 	val (thm1,thm2) = dest_thm hol_post *)
(* 	val cn_el = strip_conj thm2 *)
(* 	val cnd_lst_lst = map post_lifter cn_el *)
(* 	val cnd_lst = map (String.concatWith " & \n") cnd_lst_lst *)
(* 	val cnd_str = String.concatWith " & \n" cnd_lst *)
(* 	val cnd_str = concat ["my_precondition:bool = \n", cnd_str] *)
(*     in *)
(* 	cnd_str *)
(*     end; *)

(* fun save_send_message_post file_name = *)
(*     let val post = gen_send_message_post() *)
(* 	val fd = TextIO.openAppend file_name *)
(*     in *)
(* 	(TextIO.output (fd, post); *)
(* 	 TextIO.closeOut fd) *)
(*     end *)
(* ; *)

(* fun gen_post arg file_name = *)
(*     case arg *)
(*      of "send" => save_send_message_post file_name *)
(* ; *)
