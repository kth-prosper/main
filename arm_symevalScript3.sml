(* ------------------------------------------------------------------------ *)
(*     ARM Machine Code Symbolic Execution and Proof                        *)
(* ------------------------------------------------------------------------ *)

val _ = new_theory "arm_symrun";

loadPath := "/NOBACKUP/workspaces/nargeskh/hol4.k.7/examples/ARM/v7/eval/" :: !loadPath;

load "arm_evalLib";
open arm_evalLib;
open arm_evalTheory;
open finite_mapTheory;
open wordsTheory arithmeticTheory numLib;


val regs_list_def = 
       Define `regs_list = 
                  TOKENS (\c. (MEM c [#","] \/ (isSpace c) )) "r0, r1, r2, r3, r4, r5, r6, r7, r8, r8_fiq, r9, r9_fiq, r10, r10_fiq, r11, r11_fiq, r12, r12_fiq, sp, sp_fiq, sp_irq, sp_svc, sp_abt, sp_und, sp_mon, lr, lr_fiq, lr_irq, lr_svc, lr_abt, lr_und, lr_mon, pc"`;

val psrs_list_def = 
       Define `psrs_list = 
                  TOKENS (\c. (MEM c [#","] \/ (isSpace c) )) "cpsr , spsr_fiq, spsr_irq, spsr_svc, spsr_mon, spsr_abt, spsr_und"`;

val options_def = 
       Define `options = 
                 regs_list ++ psrs_list ++   ["arch"; "reg_default"; "psr_default"; "mem_default"]`;

val mk_free_config_map_def = 
 Define ` mk_free_config_map l s mp=
                   case l of 
                     ( x::l' ->
                        (case s of
                          y::s' -> mk_free_config_map l' s' (FUPDATE mp (x,y)) 
                           || [] -> ("not a valid free variable list" , NONE)))
                      || _ ->
                        (case s of
                          y::s' -> ("not a valid free variable list",NONE) 
                           || _ -> ("",SOME mp)) `;

val convert_to_map_def = 
 Define ` convert_to_map l mp opt =
            case  l of 
	     	(x::l' ->
                   let lr = HD(x) in 
        	   let v = HD(TL(x)) in
                   if (MEM lr opt) 
                         then convert_to_map l' (finite_map$FUPDATE mp (lr,v)) opt
        	   else
                         ("invalid option" ++ lr,NONE)
                ) 
		    || _ -> ("", SOME mp)`;

val mk_config_map_def = 
 Define ` mk_config_map opt s=
     let t = TOKENS (\c. (MEM c [#","] \/ MEM c [#";"])) s in
     let l = MAP (TOKENS (\c. ((c = (#"=")) \/ (isSpace c )))) t in
     	     convert_to_map l FEMPTY opt`;

val mk_word32_def  = Define ` mk_word32 s = (word_from_hex_string s):word32 `;
val mk_word8_def  = Define ` mk_word8 s = (word_from_hex_string s):word8 `;

val lookup_reg_map_def = 
           Define `lookup_reg_map mp fmap s = 
                         case FLOOKUP mp s
                             of  SOME tm -> mk_word32 tm
                              || NONE  -> 
                                  (case FLOOKUP fmap s of
                                       SOME tm -> tm) `;

val regs_init_def = 
      Define ` regs_init mp fmap = let 
      	       	    rv = MAP (\r. lookup_reg_map mp fmap r) regs_list
                    in RName_case  (EL 0 rv)
				   (EL 1 rv)
                                   (EL 2 rv)
				   (EL 3 rv)
				   (EL 4 rv) 
				   (EL 5 rv) 
				   (EL 6 rv) 
				   (EL 7 rv) 
				   (EL 8 rv) 
				   (EL 9 rv) 
				   (EL 10 rv) 
				   (EL 11 rv)  
				   (EL 12 rv)  
				   (EL 13 rv)  
				   (EL 14 rv)  
				   (EL 15 rv)  
				   (EL 16 rv)  
				   (EL 17 rv)  
				   (EL 18 rv)  
				   (EL 19 rv)  
				   (EL 20 rv)  
				   (EL 21 rv)  
				   (EL 22 rv)  
				   (EL 23 rv)  
				   (EL 24 rv)  
				   (EL 25 rv)  
				   (EL 26 rv)  
				   (EL 27 rv)  
				   (EL 28 rv)  
				   (EL 29 rv)  
				   (EL 30 rv)  
				   (EL 31 rv)  
				   (EL 32 rv)`; 

val lookup_psrs_map_def = 
           Define `lookup_psrs_map mp s psr_default = 
                         case FLOOKUP mp s
                             of  SOME tm -> 	 mk_word32 tm 
                              || NONE  -> psr_default `;

(* this version sets all the values to the default
// should be modified to work like regsiters
*)

val psrs_init_def = 
      Define ` psrs_init psr_default= (*let 
      	       	    rv = MAP (\r. lookup_psrs_map mp r psr_default) psrs_list
                     in *) PSRName_case psr_default psr_default psr_default psr_default psr_default psr_default psr_default `; 

(* reading the free variales as a record instead of list*)

 val sym_configure_def = 
       Define `sym_configure s l=
           let cmap = mk_config_map options s in
           let fmap = mk_free_config_map regs_list l FEMPTY in
           case cmap of 
              (msg, SOME mp) ->
                  let default_reg = 
                     case FLOOKUP mp "reg_default"
                          of SOME tm ->  (mk_word32 tm ) 
                            || NONE  -> (mk_word32 "0" ) in
                   let default_psr = 
                     case FLOOKUP mp "psr_default"
                         of SOME tm ->  (arm_coretypes$decode_psr (mk_word32 tm )) 
                         || NONE ->  (arm_coretypes$decode_psr (mk_word32 ("0"))) in 
                   let default_mem = 
                     case FAPPLY mp "mem_default"
                         of tm ->  (mk_word8 tm ) 
                         || _ ->  (mk_word8 "0") in                   
		   (case fmap of (msg,SOME fmp) ->
                	 ((case (FAPPLY mp "arch")
                             of "armv4"   -> arm_coretypes$ARMv4
                             || "armv4t"  -> arm_coretypes$ARMv4T
                             || "armv5t"  -> arm_coretypes$ARMv5T
                             || "armv5te" -> arm_coretypes$ARMv5TE
                             || "armv6"   -> arm_coretypes$ARMv6
                             || "armv6k"  -> arm_coretypes$ARMv6K
                             || "armv6t2" -> arm_coretypes$ARMv6T2
                             || "armv7-a" -> arm_coretypes$ARMv7_A
                             || "armv7-r" -> arm_coretypes$ARMv7_R
                             || _ -> ARMv7_A),
			  regs_init mp fmp,
			  psrs_init default_psr,
			  default_mem))`;

val mk_arm_state_def = Define `
  mk_arm_state arch regs psrs md mem =
    <| registers := proc 0 regs;
       psrs := proc 0 psrs;
       event_register := (K T);
       interrupt_wait := (K F);
       memory := (\a. case patricia$PEEK mem (w2n a)
                        of SOME d -> d
                        || NONE -> md);
       accesses := [];
       information := <| arch := arch;
                         unaligned_support := T;
                         extensions := {} |>;
       (* coprocessors updated_by *)
       (*   (Coprocessors_state_fupd *)
       (*      (cp15_fupd (CP15reg_SCTLR_fupd *)
       (*        (\sctlr. sctlr with <| V := F; A := T; U := F; *)
       (*                               IE := T; TE := F; NMFI := T; *)
       (*                               EE := T; VE := F |>)) o *)
       (*       cp14_fupd (CP14reg_TEEHBR_fupd (K 0xF0000000w)))); *)
       monitors := <| ClearExclusiveByAddress := (K (constE ()))|>; 
		   status := F  |>`;





val valid_state_def = Define `is_valid_state s = s.status `;

val write_status_def = Define`
  write_status s d = s with status := d`;


val init_state_def =
       Define `init_state s l prog =
             let  (arch,reg,psr,mem) = sym_configure s l in
		 mk_arm_state arch reg psr mem prog `;


val ground_init_state_def =
       Define `ground_init_state s l prog =
             let def_regs = [0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 
			     0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 
			     0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 
			     0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w] in
		 let  (arch,reg,psr,mem) = 
		  sym_configure s def_regs in
		 mk_arm_state arch reg psr mem prog `;

val _ = export_theory ();

(* symbolic execution of the program *)
(*to be done: fix the exit points of the program*)

val arm_sym_run_def =
       Define `arm_sym_run s0 prog n exit_pc=
	     let sf = ptree_arm_run prog s0 n in
             case sf of 
		 (msg, SOME (state:arm_state)) -> 
                     case msg of 
		       "finished" -> (write_status state T):arm_state
                     ||
		   	("couldn't fetch an instruction" -> 
                           ( let r15 = read_pc (<| proc := 0 |>) state in 
				 case r15 of 
				     ValueState pc s -> 
				        if (pc = exit_pc ) then
	         (* ("exit point: couldn't fetch an instruction")*)  
                                          (write_status state T):arm_state
					else
      (*"error: couldn't fetch an instruction at ",*)state:arm_state))
                     || _ -> state `;


(* theorems for proof *)
(* one-step theorem *)
val next_def =
       Define `next s prog exit_pc = arm_sym_run s prog 1 exit_pc`;
  


val cycles_num_def = Define `cycles_num s = case s of (state, prog , cycle, exit_pc) -> cycle `;


(*---------- another version ----------*)
val stepsv_def_1 =
       Define `stepsv s prog 0 exit_pc = s`;

(* should be modified to report the exact point of failure*)

val stepsv_def_2 =
       Hol_defn "Nstepsv" `stepsv s prog (n:num) exit_pc = 
                if (n > 0) then 
                    next (stepsv s prog (n-1) exit_pc) prog exit_pc 
                else 
                       s`;     

val stepsv_def_2 =  tDefine "Nstepsv" `stepsv s prog (n:num) exit_pc = 
                if (n > 0) then 
                     next (stepsv s prog (n-1) exit_pc) prog exit_pc
                else 
                       s`
   (WF_REL_TAC `measure cycles_num` THEN EVAL_TAC THEN (REPEAT GEN_TAC) THEN RW_TAC arith_ss [SUB_LESS_EQ]);


(* ========================================================================== *)
(*                      Evaluation: a program with no loop                    *)
(* ========================================================================== *)


(* ----- loading the program in the address range of 2816 to 2839 ----------- *)
val evals1 =       arm_load_from_file "B00" "/NOBACKUP/workspaces/nargeskh/hol4.k.7/examples/ARM/v7/verification/prog.s" arm_load_empty
                      |> fst
                      |> patriciaLib.Define_mk_ptree "poly_prog";

val it = arm_step "v4T,fiq,big-endian,pass,arm" "ee083f17"

val evals2 =      arm_load_from_string "B00" "mcr p15, #1, R2, c4, c7, #3" arm_load_empty
                      |> fst
                      |> patriciaLib.Define_mk_ptree "poly_prog";


(* --------------------- checking assertions --------------------------------- *)
val s0= EVAL ``   init_state "pc=B00,arch=armv7,mem_default=0" 
                      [r0; r1; r2; r3; r4; r5; r6; r7; r8; 
                       r8_fiq; r9; r9_fiq; r10; r10_fiq; r11; r11_fiq; r12; 
                       r12_fiq; sp; sp_fiq; sp_irq; sp_svc; sp_abt; sp_und; sp_mon; 
                       lr; lr_fiq; lr_irq; lr_svc; lr_abt; lr_und; lr_mon; pc] poly_prog ``;

val s0= EVAL `` let s0 = init_state "pc=B00,arch=armv7,mem_default=0" 
                      [r0; r1; r2; r3; r4; r5; r6; r7; r8; 
                       r8_fiq; r9; r9_fiq; r10; r10_fiq; r11; r11_fiq; r12; 
                       r12_fiq; sp; sp_fiq; sp_irq; sp_svc; sp_abt; sp_und; sp_mon; 
                       lr; lr_fiq; lr_irq; lr_svc; lr_abt; lr_und; lr_mon; pc] poly_prog 
in
let sf =   next s0 poly_prog 2829w
 in read_sctlr <| proc := 0 |> sf ``;

g ` !n. let s0 =  init_state "arch=armv7" 
                      [r0; r1; r2; r3; r4; r5; r6; r7; r8; 
                       r8_fiq; r9; r9_fiq; r10; r10_fiq; r11; r11_fiq; r12; 
                       r12_fiq; sp; sp_fiq; sp_irq; sp_svc; sp_abt; sp_und; sp_mon; 
                       lr; lr_fiq; lr_irq; lr_svc; lr_abt; lr_und; lr_mon; 2824w] poly_prog  in
     let sf = stepsv s0 poly_prog n 2840w in
	 ((is_valid_state sf) /\ (ARM_READ_REG 15w sf = 2824w)) ==>
                    (ARM_READ_REG 2w sf = (5w*r1)) `;

g ` !n. let sf = stepsv ^s0 poly_prog n 2840w in
        let sf.memory = ^s0.memory in
		    ((is_valid_state sf) /\ (ARM_READ_REG 15w sf = 2824w)) ==>
                    (ARM_READ_REG 2w sf = (5w*r1)) `;

e (Induct_on `n`);
e (EVAL_TAC);
e (PURE_ONCE_REWRITE_TAC [stepsv_def_2]); (*goal rewriting*)
e (RW_TAC arith_ss [NOT_SUC_LESS_EQ_0]);
e (Cases_on `is_valid_state sf`);
e (EVAL_TAC);
e (FULL_SIMP_TAC bool_ss [COND_EXPAND]); (*assumptions simplification*)
e (FULL_SIMP_TAC std_ss [valid_state_def]);

e(Q.UNABBREV_TAC `sf`);

(*--------lemma for proving the above theorem ----------*)

val Non_Equal_PC_thm = store_thm("Non_Equal_PC_thm",
  ``! s.  let s = 
          init_state "arch=armv7" 
                      [r0; r1; r2; r3; r4; r5; r6; r7; r8; 
                       r8_fiq; r9; r9_fiq; r10; r10_fiq; r11; r11_fiq; r12; 
                       r12_fiq; sp; sp_fiq; sp_irq; sp_svc; sp_abt; sp_und; sp_mon; 
                       lr; lr_fiq; lr_irq; lr_svc; lr_abt; lr_und; lr_mon; 2824w] poly_prog in
let sf = next s poly_prog exit_pc in ARM_READ_REG 15w sf <> 2824w ``, EVAL_TAC);

(*the new version of equation*)
load "arm_seq_monadTheory"

g `
let s = <| registers :=
          proc 0
            (RName_case r0vl n r2 r3 r4 r5 r6 r7 r8
               r8_fiq r9 r9_fiq r10 r10_fiq r11 r11_fiq
               r12 r12_fiq sp sp_fiq sp_irq sp_svc sp_abt
               sp_und sp_mon lr lr_fiq lr_irq lr_svc
               lr_abt lr_und lr_mon pc);
        psrs := psrs_val;
        event_register := event_register_val; 
        interrupt_wait := interrupt_wait_val;
        memory :=
          (\a. case fact_prog ' (w2n a) of NONE => 0w | SOME d => d);
        accesses := accesses_val;
        information := information_val |> 
in  
let pc = 2824w in
let sf = next s poly_prog exit_pc in 
ARM_READ_REG 15w sf <> 2824w `;

e (FULL_SIMP_TAC bool_ss [next_def]); (*assumptions simplification*)
e (FULL_SIMP_TAC std_ss [arm_sym_run_def]); (*assumptions simplification*)
e (FULL_SIMP_TAC std_ss [ptree_arm_run_def]); (*assumptions simplification*)
e (FULL_SIMP_TAC std_ss [ptree_arm_loop_def]); (*assumptions simplification*)


(*------------------      --------------------*)


(* proof of non-self- modifying code *)
g ` !n. let s0 = 
          init_state "pc=B00,arch=armv7,mem_default=0" 
                      [r0; r1; r2; r3; r4; r5; r6; r7; r8; 
                       r8_fiq; r9; r9_fiq; r10; r10_fiq; r11; r11_fiq; r12; 
                       r12_fiq; sp; sp_fiq; sp_irq; sp_svc; sp_abt; sp_und; sp_mon; 
                       lr; lr_fiq; lr_irq; lr_svc; lr_abt; lr_und; lr_mon; pc] poly_prog in 
	let sf = stepsv s0 poly_prog n 2840w in
          sf.memory = s0.memory`;


e (Induct_on `n`);
e (EVAL_TAC);
e (PURE_ONCE_REWRITE_TAC [stepsv_def_2]); (*goal rewriting*)
e (RW_TAC arith_ss [NOT_SUC_LESS_EQ_0]);
e (Q.UNABBREV_TAC `sf'`);
e (Cases_on `is_valid_state sf`);
e (EVAL_TAC);
e (FULL_SIMP_TAC bool_ss [COND_EXPAND]); (*assumptions simplification*)
e (FULL_SIMP_TAC std_ss [valid_state_def]);


(*------the pc range --------------*)

g `!n. let s0 = 
          init_state "pc=B00,arch=armv7,mem_default=0" 
                      [r0; r1; r2; r3; r4; r5; r6; r7; r8; 
                       r8_fiq; r9; r9_fiq; r10; r10_fiq; r11; r11_fiq; r12; 
                       r12_fiq; sp; sp_fiq; sp_irq; sp_svc; sp_abt; sp_und; sp_mon; 
                       lr; lr_fiq; lr_irq; lr_svc; lr_abt; lr_und; lr_mon; pc] poly_prog in 
	let sf = stepsv s0 poly_prog n 2840w in
        let pc = ARM_READ_REG 15w sf in
          (pc=2816w) \/ (pc=2820w)`;


e (Induct_on `n`);
e (EVAL_TAC);
e (PURE_ONCE_REWRITE_TAC [stepsv_def_2]); (*goal rewriting*)
e (RW_TAC arith_ss [NOT_SUC_LESS_EQ_0]);
e(Cases_on `ARM_READ_REG 15w sf`)
e (FULL_SIMP_TAC bool_ss []); (*assumptions simplification*)


   (ARM_READ_REG 15w sf) ==>
 sf =
            


e(Q.UNABBREV_TAC `pc'`);
e (Cases_on `is_valid_state sf`);
e (EVAL_TAC);
e (FULL_SIMP_TAC bool_ss [COND_EXPAND]); (*assumptions simplification*)
e (FULL_SIMP_TAC std_ss [valid_state_def]);


(* --------------------- check on exit --------------------------------- *)

val poly_exit = store_thm("poly_exit",
  `` let s0 = 
          init_state "pc=B00,arch=armv7,mem_default=0" 
                      [r0; r1; r2; r3; r4; r5; r6; r7; r8; 
                       r8_fiq; r9; r9_fiq; r10; r10_fiq; r11; r11_fiq; r12; 
                       r12_fiq; sp; sp_fiq; sp_irq; sp_svc; sp_abt; sp_und; sp_mon; 
                       lr; lr_fiq; lr_irq; lr_svc; lr_abt; lr_und; lr_mon; pc] poly_prog in 
	let sf = steps s0 poly_prog 6 2840w in
		    (is_valid_state sf) /\ (ARM_READ_REG 2w sf > (15w*r1)) ``,
EVAL_TAC THEN METIS_TAC [WORD_MULT_CLAUSES] );

(* --------------------- executing the program --------------------------------- *)

EVAL `` let s0 = 
          init_state "pc=B00,arch=armv7,mem_default=0" 
                      [r0; r1; r2; r3; r4; r5; r6; r7; r8; 
                       r8_fiq; r9; r9_fiq; r10; r10_fiq; r11; r11_fiq; r12; 
                       r12_fiq; sp; sp_fiq; sp_irq; sp_svc; sp_abt; sp_und; sp_mon; 
                       lr; lr_fiq; lr_irq; lr_svc; lr_abt; lr_und; lr_mon; pc] poly_prog in  steps s0 poly_prog 6 2840w ``;


(* ========================================================================== *)
(*                      Evaluation: a program with loop                    *)
(* ========================================================================== *)

g `!n . let s0 = 
          init_state "pc=A00,arch=armv7,mem_default=0" 
                      [r0; r1; r2; r3; r4; r5; r6; r7; r8; 
                       r8_fiq; r9; r9_fiq; r10; r10_fiq; r11; r11_fiq; r12; 
                       r12_fiq; sp; sp_fiq; sp_irq; sp_svc; sp_abt; sp_und; sp_mon; 
                       lr; lr_fiq; lr_irq; lr_svc; lr_abt; lr_und; lr_mon; pc] fact_prog in 
let sf = steps s0 fact_prog 1 2580w in
    (ARM_READ_REG 15w sf = 2579w) ==> 
              (?m . (m<=n) /\ let sf' = steps s0 fact_prog 1 2580w in ARM_READ_REG 2w sf'  0w) `;



EVAL ``sym_configure "pc=A00,arch=armv7,mem_default=0" [r0; r1; r2; r3; r4; r5; r6; r7; r8; r8_fiq; r9; r9_fiq; r10; r10_fiq; r11; r11_fiq; r12; r12_fiq; sp; sp_fiq; sp_irq; sp_svc; sp_abt; sp_und; sp_mon; lr; lr_fiq; lr_irq; lr_svc; lr_abt; lr_und; lr_mon; pc]``;

EVAL ``arm_sym_run s0 fact_prog 1 2580w``;

!n. let sf = arm_sym_run "pc=A00,arch=armv7,mem_default=0" [r0; r1; r2; r3; r4; r5; r6; r7; r8; r8_fiq; r9; r9_fiq; r10; r10_fiq; r11; r11_fiq; r12; r12_fiq; sp; sp_fiq; sp_irq; sp_svc; sp_abt; sp_und; sp_mon; lr; lr_fiq; lr_irq; lr_svc; lr_abt; lr_und; lr_mon; pc] fact_prog n 2580w in 
(ARM_READ_REG 2w sf) >= 5w 


METIS_TAC [DECIDE ``theorem about falsification``]


