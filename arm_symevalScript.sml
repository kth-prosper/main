(* ------------------------------------------------------------------------ *)
(*     ARM Machine Code Symbolic Execution and Proof                        *)
(* ------------------------------------------------------------------------ *)

val _ = new_theory "arm_symrun";

loadPath := "/NObackup/WORKSPACES/NARGESKH/hol4.k.7/examples/ARM/v7/eval/" :: !loadPath;

load "arm_evalTheory";
open arm_evalTheory;
open finite_mapTheory wordsTheory arithmeticTheory numLib;


(*for loading the program in the memory*)
load "arm_evalLib";
open arm_evalLib;

val regs = ``(RName_case (r0:bool[32]) r1 r2 r3 r4 r5 r6 r7 r8 r8_fiq r9 r9_fiq r10
	     r10_fiq r11 r11_fiq r12 r12_fiq sp sp_fiq sp_irq sp_svc
	     sp_abt sp_und sp_mon lr lr_fiq lr_irq lr_svc lr_abt
             lr_und lr_mon pc)``;

val psr_default = `` <|N := n; Z := z; C := c; V := v; Q := q; IT := it; J := j;
              Reserved := rsv; GE := ge; E := e; A := a; I := i; F := f;
              T := f; M := m|>``;

val psrs = ``PSRName_case ^psr_default ^psr_default ^psr_default ^psr_default ^psr_default ^psr_default ^psr_default``;

val md = ``md:bool[8]``;

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
       coprocessors updated_by
         (Coprocessors_state_fupd
            (cp15_fupd (CP15reg_SCTLR_fupd
              (\sctlr. sctlr with <| V := F; A := T; U := F;
                                     IE := T; TE := F; NMFI := T;
                                     EE := T; VE := F |>)) o
             cp14_fupd (CP14reg_TEEHBR_fupd (K 0xF0000000w))));
       monitors := <| ClearExclusiveByAddress := (K (constE ()))|>; 
		   status := F  |>`;

val init_state_def =
       Define `init_state arch prog =
		 mk_arm_state arch ^regs ^psrs ^md prog `;


val valid_state_def = Define `is_valid_state s = s.status `;

val write_status_def = Define`
  write_status s d = s with status := d`;

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

val next_def =
       Define `next s prog exit_pc = arm_sym_run s prog 1 exit_pc`;

(*_____________the second definition of steps---------------*)

val cycles_num_def = Define `cycles_num s = case s of (state, prog , cycle, exit_pc) -> cycle `;

val steps_def_1 =
       Define `steps s prog 0 exit_pc = s`;

(* should be modified to report the exact point of failure*)

val steps_def_2 =
       Hol_defn "Nsteps" `steps s prog (n:num) exit_pc = 
                if (n > 0) then 
                    steps (next s prog exit_pc) prog (n-1) exit_pc 
                else 
                 s`;   

Defn.tgoal steps_def_2;

val steps_def_2 =  tDefine "Nsteps"
   `steps s prog (n:num) exit_pc = 
                if (n > 0) then 
                      steps (next s prog exit_pc) prog (n-1) exit_pc 
                else 
                       s`
   (WF_REL_TAC `measure cycles_num` THEN EVAL_TAC THEN (REPEAT GEN_TAC) THEN RW_TAC arith_ss [SUB_LESS_EQ]);

(** loaded in the address range of 2560 to 2583 **)
val evals1 =       arm_load_from_file "A00" "/NOBACKUP/workspaces/nargeskh/hol4.k.7/examples/ARM/v7/verification/prog.s" arm_load_empty
                      |> fst
                      |> patriciaLib.Define_mk_ptree "poly_prog";



(* ========================================================================== *)
(*                      Evaluation: a program with no loop                    *)
(* ========================================================================== *)
val s0 = EVAL ``s0 =  mk_arm_state ARMv7_R 
             (RName_case r0 r1 r2 r3 r4 r5 r6 r7 r8 r8_fiq r9 r9_fiq r10
	     r10_fiq r11 r11_fiq r12 r12_fiq sp sp_fiq sp_irq sp_svc
	     sp_abt sp_und sp_mon lr lr_fiq lr_irq lr_svc lr_abt
             lr_und lr_mon pc) ^psrs md poly_prog``;

g ` !n.  let  mk_arm_state ARMv7_R 
             (RName_case r0 r1 r2 r3 r4 r5 r6 r7 r8 r8_fiq r9 r9_fiq r10
	     r10_fiq r11 r11_fiq r12 r12_fiq sp sp_fiq sp_irq sp_svc
	     sp_abt sp_und sp_mon lr lr_fiq lr_irq lr_svc lr_abt
             lr_und lr_mon pc) psrs md poly_prog in
         let sf = (steps ^s0 poly_prog n 28w) in
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
  `` let s = 
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
e(Q.UNABBREV_TAC `sf'`);
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

val simpleThm = store_thm("simple",
  `` !n. let sf = arm_sym_run "pc=A00,arch=armv7,mem_default=0" [r0; r1; r2; r3; r4; r5; r6; r7; r8; r8_fiq; r9; r9_fiq; r10; r10_fiq; r11; r11_fiq; r12; r12_fiq; sp; sp_fiq; sp_irq; sp_svc; sp_abt; sp_und; sp_mon; lr; lr_fiq; lr_irq; lr_svc; lr_abt; lr_und; lr_mon; pc] fact_prog n 2580w in 
(ARM_READ_REG 2w sf) >= 5w ``,
EVAL_TAC)

!n. let sf = arm_sym_run "pc=A00,arch=armv7,mem_default=0" [r0; r1; r2; r3; r4; r5; r6; r7; r8; r8_fiq; r9; r9_fiq; r10; r10_fiq; r11; r11_fiq; r12; r12_fiq; sp; sp_fiq; sp_irq; sp_svc; sp_abt; sp_und; sp_mon; lr; lr_fiq; lr_irq; lr_svc; lr_abt; lr_und; lr_mon; pc] fact_prog n 2580w in 
(ARM_READ_REG 2w sf) >= 5w 


METIS_TAC [DECIDE ``theorem about falsification``]

