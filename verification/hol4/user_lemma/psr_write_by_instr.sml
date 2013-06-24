(* cpsr_write_by_instr *)


val cpsr_write_by_instr_part1 =
``(λ(priviledged,is_secure,nsacr,badmode).
    if
      (bytemask:word4) ' 0 ∧ priviledged ∧
      (badmode ∨ ¬is_secure ∧ ((((4 >< 0) (value:word32)):word5)= 22w) ∨
       ¬is_secure ∧ ((((4 >< 0) value):word5) = 17w) ∧ nsacr.RFR)
    then
      errorT "cpsr_write_by_instr: unpredictable"
    else
      (read_sctlr <|proc := 0|> ||| read_scr <|proc := 0|>
         ||| read_cpsr <|proc := 0|>) >>=
      (λ(sctlr,scr,cpsr).
         write_cpsr <|proc := 0|>
           (cpsr with
            <|N := if bytemask ' 3 then value ' 31 else cpsr.N;
              Z := if bytemask ' 3 then value ' 30 else cpsr.Z;
              C := if bytemask ' 3 then value ' 29 else cpsr.C;
              V := if bytemask ' 3 then value ' 28 else cpsr.V;
              Q := if bytemask ' 3 then value ' 27 else cpsr.Q;
              IT :=
                if affect_execstate then
                  if bytemask ' 3 then
                    if bytemask ' 1 then
                        (((15 >< 10) value):word6) @@ (((26 >< 25) value):word2)
                        else
                          (((7 >< 2) cpsr.IT):word6) @@ (((26 >< 25) value):word2)
                      else if bytemask ' 1 then
                         (((15 >< 10) value):word6) @@ (((1 >< 0) cpsr.IT):word2)
                  else
                    cpsr.IT
                else
                  cpsr.IT;
              J :=  if bytemask ' 3 ∧ affect_execstate then value ' 24  else cpsr.J;
              GE := if bytemask ' 2 then (19 >< 16) value else cpsr.GE;
              E := if bytemask ' 1 then value ' 9 else cpsr.E;
              A :=  if  bytemask ' 1 ∧ priviledged ∧ (is_secure ∨ scr.AW) then  value ' 8 else  cpsr.A;
              I :=  if bytemask ' 0 ∧ priviledged then value ' 7 else cpsr.I;
              F :=  if bytemask ' 0 ∧ priviledged ∧ (is_secure ∨ scr.FW) /\ (¬sctlr.NMFI ∨ ¬value ' 6) then value ' 6 else cpsr.F;
              T := if bytemask ' 0 ∧ affect_execstate then value ' 5 else cpsr.T;
              M := if bytemask ' 0 ∧ priviledged then (4 >< 0) value else cpsr.M|>)))
       :(bool # bool # CP15nsacr # bool -> unit M)``;


val cpsr_write_by_instr_part2 = 
``(λ(sctlr,scr,cpsr).
             write_cpsr <|proc := 0|>
               (cpsr with
                <|N := if bytemask ' 3 then value ' 31 else cpsr.N;
                  Z := if bytemask ' 3 then value ' 30 else cpsr.Z;
                  C := if bytemask ' 3 then value ' 29 else cpsr.C;
                  V := if bytemask ' 3 then value ' 28 else cpsr.V;
                  Q := if bytemask ' 3 then value ' 27 else cpsr.Q;
                  IT :=
                    if affect_execstate then
                      if bytemask ' 3 then
                        if bytemask ' 1 then
                          (((15 >< 10) value):word6) @@ (((26 >< 25) value):word2)
                        else
                          (((7 >< 2) cpsr.IT):word6) @@ (((26 >< 25) value):word2)
                      else if bytemask ' 1 then
                         (((15 >< 10) value):word6) @@ (((1 >< 0) cpsr.IT):word2)
                      else
                        cpsr.IT
                    else
                      cpsr.IT;
                  J :=
                    if bytemask ' 3 ∧ affect_execstate then
                      value ' 24
                    else
                      cpsr.J;
                  GE :=
                    if bytemask ' 2 then (19 >< 16) value else cpsr.GE;
                  E := if bytemask ' 1 then value ' 9 else cpsr.E;
                  A := cpsr.A; I := cpsr.I; F := cpsr.F;
                  T :=
                    if bytemask ' 0 ∧ affect_execstate then
                      value ' 5
                    else
                      cpsr.T; M := cpsr.M|>))
          :(CP15sctlr # CP15scr # ARMpsr -> unit M)``;

val cpsr_write_by_instr_components_without_mode = `` (cpsr with
                <|N := if bytemask ' 3 then value ' 31 else cpsr.N;
                  Z := if bytemask ' 3 then value ' 30 else cpsr.Z;
                  C := if bytemask ' 3 then value ' 29 else cpsr.C;
                  V := if bytemask ' 3 then value ' 28 else cpsr.V;
                  Q := if bytemask ' 3 then value ' 27 else cpsr.Q;
                  IT :=
                    if affect_execstate then
                      if bytemask ' 3 then
                        if bytemask ' 1 then
                          (((15 >< 10) value):word6) @@ (((26 >< 25) value):word2)
                        else
                          (((7 >< 2) cpsr.IT):word6) @@ (((26 >< 25) value):word2)
                      else if bytemask ' 1 then
                         (((15 >< 10) value):word6) @@ (((1 >< 0) cpsr.IT):word2)
                      else
                        cpsr.IT
                    else
                      cpsr.IT;
                  J :=  if bytemask ' 3 ∧ affect_execstate then value ' 24 else cpsr.J;
                  GE := if bytemask ' 2 then (19 >< 16) value else cpsr.GE;
                  E := if bytemask ' 1 then value ' 9 else cpsr.E;
                  A := cpsr.A; I := cpsr.I; F := cpsr.F;
                  T :=  if bytemask ' 0 ∧ affect_execstate then value ' 5 else cpsr.T|>)``;

val cpsr_write_by_instr_components_without_IFM = `` (cpsr with
                <|N := if bytemask ' 3 then value ' 31 else cpsr.N;
                  Z := if bytemask ' 3 then value ' 30 else cpsr.Z;
                  C := if bytemask ' 3 then value ' 29 else cpsr.C;
                  V := if bytemask ' 3 then value ' 28 else cpsr.V;
                  Q := if bytemask ' 3 then value ' 27 else cpsr.Q;
                  IT :=
                    if affect_execstate then
                      if bytemask ' 3 then
                        if bytemask ' 1 then
                          (((15 >< 10) value):word6) @@ (((26 >< 25) value):word2)
                        else
                          (((7 >< 2) cpsr.IT):word6) @@ (((26 >< 25) value):word2)
                      else if bytemask ' 1 then
                         (((15 >< 10) value):word6) @@ (((1 >< 0) cpsr.IT):word2)
                      else
                        cpsr.IT
                    else
                      cpsr.IT;
                  J :=  if bytemask ' 3 ∧ affect_execstate then value ' 24 else cpsr.J;
                  GE := if bytemask ' 2 then (19 >< 16) value else cpsr.GE;
                  E := if bytemask ' 1 then value ' 9 else cpsr.E;
                  A := cpsr.A;
                  T :=  if bytemask ' 0 ∧ affect_execstate then value ' 5 else cpsr.T|>)``;


val cpsr_write_by_instr_components_with_mode = `` (cpsr with
                <|N := if bytemask ' 3 then value ' 31 else cpsr.N;
                  Z := if bytemask ' 3 then value ' 30 else cpsr.Z;
                  C := if bytemask ' 3 then value ' 29 else cpsr.C;
                  V := if bytemask ' 3 then value ' 28 else cpsr.V;
                  Q := if bytemask ' 3 then value ' 27 else cpsr.Q;
                  IT :=
                    if affect_execstate then
                      if bytemask ' 3 then
                        if bytemask ' 1 then
                          (((15 >< 10) value):word6) @@ (((26 >< 25) value):word2)
                        else
                          (((7 >< 2) cpsr.IT):word6) @@ (((26 >< 25) value):word2)
                      else if bytemask ' 1 then
                         (((15 >< 10) value):word6) @@ (((1 >< 0) cpsr.IT):word2)
                      else
                        cpsr.IT
                    else
                      cpsr.IT;
                  J :=  if bytemask ' 3 ∧ affect_execstate then value ' 24 else cpsr.J;
                  GE := if bytemask ' 2 then (19 >< 16) value else cpsr.GE;
                  E := if bytemask ' 1 then value ' 9 else cpsr.E;
                  A := cpsr.A; I := cpsr.I; F := cpsr.F;
                  T :=  if bytemask ' 0 ∧ affect_execstate then value ' 5 else cpsr.T;
                  M := 16w|>)``;


val cpsr_write_by_instr_components_complete = `` (cpsr with
                <|N := if bytemask ' 3 then value ' 31 else cpsr.N;
                  Z := if bytemask ' 3 then value ' 30 else cpsr.Z;
                  C := if bytemask ' 3 then value ' 29 else cpsr.C;
                  V := if bytemask ' 3 then value ' 28 else cpsr.V;
                  Q := if bytemask ' 3 then value ' 27 else cpsr.Q;
                  IT :=
                    if affect_execstate then
                      if bytemask ' 3 then
                        if bytemask ' 1 then
                          (((15 >< 10) value):word6) @@ (((26 >< 25) value):word2)
                        else
                          (((7 >< 2) cpsr.IT):word6) @@ (((26 >< 25) value):word2)
                      else if bytemask ' 1 then
                         (((15 >< 10) value):word6) @@ (((1 >< 0) cpsr.IT):word2)
                      else
                        cpsr.IT
                    else
                      cpsr.IT;
                  J :=  if bytemask ' 3 ∧ affect_execstate then value ' 24 else cpsr.J;
                  GE := if bytemask ' 2 then (19 >< 16) value else cpsr.GE;
                  E := if bytemask ' 1 then value ' 9 else cpsr.E;
                  A := cpsr.A; I := xI; F := xF;
                  T :=  if bytemask ' 0 ∧ affect_execstate then value ' 5 else cpsr.T;
                  M := 16w|>)``;


val cpsr_write_by_instr_unpriv_def = Define `cpsr_write_by_instr_unpriv (value:word32, bytemask:word4, affect_execstate:bool) = ((current_mode_is_priviledged <|proc := 0|> 
          ||| is_secure <|proc := 0|> ||| read_nsacr <|proc := 0|>
          ||| bad_mode <|proc := 0|> ((4 >< 0) value)) >>=
       (λ(p,s,n,b).
          (read_sctlr <|proc := 0|> ||| read_scr <|proc := 0|>
             ||| read_cpsr <|proc := 0|>) >>=
          (λ(sctlr,scr,cpsr).
             write_cpsr <|proc := 0|>
               (cpsr with
                <|N := if bytemask ' 3 then value ' 31 else cpsr.N;
                  Z := if bytemask ' 3 then value ' 30 else cpsr.Z;
                  C := if bytemask ' 3 then value ' 29 else cpsr.C;
                  V := if bytemask ' 3 then value ' 28 else cpsr.V;
                  Q := if bytemask ' 3 then value ' 27 else cpsr.Q;
                  IT :=
                    if affect_execstate then
                      if bytemask ' 3 then
                        if bytemask ' 1 then
                          (((15 >< 10) value):word6) @@ (((26 >< 25) value):word2)
                        else
                          (((7 >< 2) cpsr.IT):word6) @@ (((26 >< 25) value):word2)
                      else if bytemask ' 1 then
                         (((15 >< 10) value):word6) @@ (((1 >< 0) cpsr.IT):word2)
                      else
                        cpsr.IT
                    else
                      cpsr.IT;
                  J :=
                    if bytemask ' 3 ∧ affect_execstate then
                      value ' 24
                    else
                      cpsr.J;
                  GE :=
                    if bytemask ' 2 then (19 >< 16) value else cpsr.GE;
                  E := if bytemask ' 1 then value ' 9 else cpsr.E;
                  A := cpsr.A; I := cpsr.I; F := cpsr.F;
                  T :=
                    if bytemask ' 0 ∧ affect_execstate then
                      value ' 5
                    else
                      cpsr.T; M := cpsr.M|>))))`;



val priv_simp_lem2 = store_thm(
    "priv_simp_lem2",
    ``!s x H . (assert_mode 16w s) ==> 
       ((((current_mode_is_priviledged <|proc:=0|> ||| is_secure <|proc:=0|> ||| read_nsacr <|proc:=0|> ||| bad_mode <|proc:=0|> x) >>= (\ (p,s,n,b). H (p,s,n,b))) s)
      = (((current_mode_is_priviledged <|proc:=0|> ||| is_secure <|proc:=0|> ||| read_nsacr <|proc:=0|> ||| bad_mode <|proc:=0|> x) >>= (\ (p,s,n,b). H (F,s,n,b))) s))``,
    EVAL_TAC THEN RW_TAC (srw_ss()) []);


val cpsr_write_by_instr_simp_lem = store_thm(
    "cpsr_write_by_instr_simp_lem",
    ``!s value bytemask affect_execstate. (assert_mode 16w s) ==> 
      (cpsr_write_by_instr <|proc:=0|> (value,bytemask,affect_execstate) s 
     = cpsr_write_by_instr_unpriv (value,bytemask,affect_execstate) s)``,
    RW_TAC (srw_ss()) [cpsr_write_by_instr, cpsr_write_by_instr_unpriv_def]
       THEN IMP_RES_TAC (SPECL [``s:arm_state``, ``((4 >< 0)(value:word32)):word5``, cpsr_write_by_instr_part1] (INST_TYPE [alpha |-> (type_of(``()``))] priv_simp_lem2))
       THEN FULL_SIMP_TAC (srw_ss()) []);


val cpsr_write_by_instr_simp_rel_lem = store_thm(
    "cpsr_write_by_instr_simp_rel_lem",
    ``!value bytemask affect_execstate uf uy. 
      (preserve_relation_mmu (cpsr_write_by_instr <|proc:=0|> (value,bytemask,affect_execstate)) (assert_mode 16w) (assert_mode 16w) uf uy)
     = (preserve_relation_mmu (cpsr_write_by_instr_unpriv (value,bytemask,affect_execstate)) (assert_mode 16w) (assert_mode 16w) uf uy)``,
    RW_TAC (srw_ss()) [cpsr_write_by_instr_simp_lem, preserve_relation_mmu_def]);


(*** >>>> ***)



g `preserve_relation_mmu
  (write_cpsr <|proc := 0|> (^cpsr_write_by_instr_components_complete)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim)`;
e (Q.ABBREV_TAC `cpsr2 = ^cpsr_write_by_instr_components_without_IFM`);
e(`^cpsr_write_by_instr_components_complete = (cpsr2) with <|I:= xI; F:= xF; M := 16w|>` by Q.UNABBREV_TAC `cpsr2` THEN FULL_SIMP_TAC (srw_ss()) []);
go_on 1;
val write_cpsr_by_instruction_all_components_thm = top_thm();
add_to_simplist (write_cpsr_by_instruction_all_components_thm);


g `(preserve_relation_mmu ((read_sctlr <|proc := 0|> ||| read_scr <|proc := 0|>
             ||| read_cpsr <|proc := 0|>) >>=
          (λ (sctlr,scr,cpsr).
             write_cpsr <|proc := 0|>
               (cpsr with
                <|N := if bytemask ' 3 then value ' 31 else cpsr.N;
                  Z := if bytemask ' 3 then value ' 30 else cpsr.Z;
                  C := if bytemask ' 3 then value ' 29 else cpsr.C;
                  V := if bytemask ' 3 then value ' 28 else cpsr.V;
                  Q := if bytemask ' 3 then value ' 27 else cpsr.Q;
                  IT :=
                    if affect_execstate then
                      if bytemask ' 3 then
                        if bytemask ' 1 then
                          (((15 >< 10) value):word6) @@ (((26 >< 25) value):word2)
                        else
                          (((7 >< 2) cpsr.IT):word6) @@ (((26 >< 25) value):word2)
                      else if bytemask ' 1 then
                         (((15 >< 10) value):word6) @@ (((1 >< 0) cpsr.IT):word2)
                      else
                        cpsr.IT
                    else
                      cpsr.IT;
                  J :=  if bytemask ' 3 ∧ affect_execstate then value ' 24 else cpsr.J;
                  GE := if bytemask ' 2 then (19 >< 16) value else cpsr.GE;
                  E := if bytemask ' 1 then value ' 9 else cpsr.E;
                  A := cpsr.A; I := cpsr.I; F := cpsr.F;
                  T :=  if bytemask ' 0 ∧ affect_execstate then value ' 5 else cpsr.T;
                  M := cpsr.M|>))) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim))`;
e(ASSUME_TAC (SPECL [cpsr_write_by_instr_part2, ``(assert_mode 16w: arm_state -> bool)``] (INST_TYPE [alpha |-> type_of (``()``)] cpsr_triple_simp_rel_ext_lem2)));
e (FULL_SIMP_TAC (srw_ss()) []);
go_on 1;
val write_cpsr_by_instruction_help_lem = top_thm();
add_to_simplist write_cpsr_by_instruction_help_lem;


g `(preserve_relation_mmu (cpsr_write_by_instr <|proc:=0|> (value,bytemask,affect_execstate)) (assert_mode 16w) (assert_mode 16w) empty_unt (fix_flags xI xF empty_sim))`;
e (FULL_SIMP_TAC (srw_ss()) [cpsr_write_by_instr_simp_rel_lem, cpsr_write_by_instr_unpriv_def]);
go_on 1;
val cpsr_write_by_instr_thm = save_thm("cpsr_write_by_instr_thm", (MATCH_MP extras_lem2 (MATCH_MP ((CONJUNCT2 (SPEC_ALL fix_flags_lem))) (GENL [``xI:bool``, ``xF:bool``] (top_thm())))));



(* spsr_write_by_instr_def *)


g `preserve_relation_mmu (spsr_write_by_instr <|proc:=0|> (vl, bm)) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim`;
e(FULL_SIMP_TAC (srw_ss()) [user_simp_par_or_and_rel_lem, spsr_write_by_instr_def]);
go_on 1;
val spsr_write_by_instr_thm = save_thm ("spsr_write_by_instr_thm", (MATCH_MP extras_lem2 (top_thm())));





