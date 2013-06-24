

val current_mode_is_user_or_system_eval_lem = store_thm(
    "current_mode_is_user_or_system_eval_lem",
    ``!s x s'.
     (assert_mode 16w s)      ==> 
     (~ (access_violation s)) ==> 
     (current_mode_is_user_or_system <|proc:=0|> s = ValueState x s')
        ==> x``,
    EVAL_TAC THEN RW_TAC (srw_ss()) []);

val current_mode_is_user_or_system_eval_lem2 = store_thm(
    "current_mode_is_user_or_system_eval_lem2",
    ``!s x s'.
     (assert_mode 16w s)      ==> 
     (current_mode_is_user_or_system <|proc:=0|> s = ValueState x s') ==>
     (~ (access_violation s')) 
        ==> x``,
    EVAL_TAC  
      THEN REPEAT STRIP_TAC
      THEN Cases_on `access_violation s` THEN FULL_SIMP_TAC (srw_ss()) []
      THENL [METIS_TAC [], UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) []]);


val priv_simp_lem = store_thm(
    "priv_simp_lem",
    ``!s ifcomp elsecomp.
      (assert_mode 16w s) ==>
      (((current_mode_is_priviledged <|proc:=0|> >>=
       (\current_mode_is_priviledged.
           if current_mode_is_priviledged then
             ifcomp
           else
             elsecomp)) s)
      =
      ((current_mode_is_priviledged <|proc:=0|> >>=
       (\current_mode_is_priviledged.
           elsecomp)) s))``,
     EVAL_TAC THEN RW_TAC (srw_ss()) []);


val user_simp_lem = store_thm(
    "user_simp_lem",
    ``!s E elsecomp.
      (assert_mode 16w s) ==>
      (((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                if is_user_or_system_mode then
                  errorT E
                else
                  elsecomp)) s)
      = 
      ((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                errorT E)) s))``,
    EVAL_TAC THEN RW_TAC (srw_ss()) []);

val user_simp_or_lem = store_thm(
    "user_simp_or_lem",
    ``!s E A elsecomp.
      (assert_mode 16w s) ==>
      (((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                if is_user_or_system_mode \/ A then
                  errorT E
                else
                  elsecomp)) s)
      = 
      ((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                errorT E)) s))``,
    EVAL_TAC THEN RW_TAC (srw_ss()) []);


val user_simp_par_or_lem = store_thm(
    "user_simp_par_or_lem",
    ``!s E A P elsecomp.
      (assert_mode 16w s) ==>
      ((((current_mode_is_user_or_system <|proc := 0|> ||| P)>>=
             (λ(is_user_or_system_mode,otherparam).
                if is_user_or_system_mode \/ A then
                  errorT E
                else
                  elsecomp)) s)
      = 
      (((current_mode_is_user_or_system <|proc := 0|> ||| P )>>=
             (λ(is_user_or_system_mode,otherparam).
                errorT E)) s))``,
    EVAL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN Cases_on `P s`
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN Cases_on `access_violation b` 
       THEN FULL_SIMP_TAC (srw_ss()) []);




val user_simp_par_or_and_lem = store_thm(
    "user_simp_par_or_and_lem",
    ``!s E A P elsecomp.
      (assert_mode 16w s) ==>
      ((((current_mode_is_user_or_system <|proc := 0|> ||| P)>>=
             (λ(is_user_or_system_mode,otherparam).
                if is_user_or_system_mode \/ (A /\ otherparam) then
                  errorT E
                else
                  elsecomp)) s)
      = 
      (((current_mode_is_user_or_system <|proc := 0|> ||| P )>>=
             (λ(is_user_or_system_mode,otherparam).
                errorT E)) s))``,
    EVAL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN Cases_on `P s`
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN Cases_on `access_violation b` 
       THEN FULL_SIMP_TAC (srw_ss()) []);


val user_simp_par_or_eqv_lem = store_thm(
    "user_simp_par_or_eqv_lem",
    ``!s E x P elsecomp.
      (assert_mode 16w s) ==>
      ((((current_mode_is_user_or_system <|proc := 0|> ||| P)>>=
             (λ(is_user_or_system_mode,otherparam).
                if is_user_or_system_mode \/ (otherparam = x) then
                  errorT E
                else
                  elsecomp)) s)
      = 
      (((current_mode_is_user_or_system <|proc := 0|> ||| P )>>=
             (λ(is_user_or_system_mode,otherparam).
                errorT E)) s))``,
    EVAL_TAC
       THEN RW_TAC (srw_ss()) []
       THEN Cases_on `P s`
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN Cases_on `access_violation b` 
       THEN FULL_SIMP_TAC (srw_ss()) []);



val priv_simp_rel_lem = store_thm(
    "priv_simp_rel_lem",
    ``!ifcomp elsecomp inv2 uf uy.
      (preserve_relation_mmu
        (current_mode_is_priviledged <|proc:=0|> >>=
          (\current_mode_is_priviledged.
           if current_mode_is_priviledged then
             ifcomp
           else
             elsecomp)) (assert_mode 16w) (inv2) uf uy)
        = 
      (preserve_relation_mmu
       (current_mode_is_priviledged <|proc:=0|> >>=
          (\current_mode_is_priviledged.
             elsecomp)) (assert_mode 16w) (inv2) uf uy)``,
     RW_TAC (srw_ss()) [priv_simp_lem, preserve_relation_mmu_def]);



val user_simp_rel_lem = store_thm(
    "user_simp_rel_lem",
    ``!E elsecomp uf uy.
      (preserve_relation_mmu
       ((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                if is_user_or_system_mode then
                  (errorT E: 'a M)
                else
                  elsecomp))) (assert_mode 16w) (assert_mode 16w) uf uy)
        = 
      (preserve_relation_mmu
       ((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                (errorT E: 'a M)))) (assert_mode 16w) (assert_mode 16w) uf uy)``,
     RW_TAC (srw_ss()) [user_simp_lem, preserve_relation_mmu_def]);


val user_simp_or_rel_lem = store_thm(
    "user_simp_or_rel_lem",
    ``!E A elsecomp uf uy.
      (preserve_relation_mmu
       ((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                if is_user_or_system_mode \/ A then
                  (errorT E: 'a M)
                else
                  elsecomp))) (assert_mode 16w) (assert_mode 16w) uf uy)
        = 
      (preserve_relation_mmu
       ((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                (errorT E: 'a M)))) (assert_mode 16w) (assert_mode 16w) uf uy)``,
     RW_TAC (srw_ss()) [user_simp_or_lem, preserve_relation_mmu_def]);


val user_simp_par_or_rel_lem = store_thm(
    "user_simp_par_or_rel_lem",
    ``!E A (P:'b M) elsecomp uf uy.
      (preserve_relation_mmu
       (((current_mode_is_user_or_system <|proc := 0|> ||| P) >>=
             (λ(is_user_or_system_mode,otherparam).
                if is_user_or_system_mode \/ A then
                  (errorT E: 'a M)
                else
                  elsecomp))) (assert_mode 16w) (assert_mode 16w) uf uy)
        = 
      (preserve_relation_mmu
       (((current_mode_is_user_or_system <|proc := 0|> ||| P)>>=
             (λ(is_user_or_system_mode,otherparam).
                (errorT E: 'a M)))) (assert_mode 16w) (assert_mode 16w) uf uy)``,
     RW_TAC (srw_ss()) [user_simp_par_or_lem, preserve_relation_mmu_def]);


val user_simp_par_or_eqv_rel_lem = store_thm(
    "user_simp_par_or_eqv_lem",
    ``!E x (P:'b M) elsecomp uf uy.
      (preserve_relation_mmu
       (((current_mode_is_user_or_system <|proc := 0|> ||| P) >>=
             (λ(is_user_or_system_mode,otherparam).
                if is_user_or_system_mode \/ (otherparam = x) then
                  (errorT E: 'a M)
                else
                  elsecomp))) (assert_mode 16w) (assert_mode 16w) uf uy)
        = 
      (preserve_relation_mmu
       (((current_mode_is_user_or_system <|proc := 0|> ||| P)>>=
             (λ(is_user_or_system_mode,otherparam).
                (errorT E: 'a M)))) (assert_mode 16w) (assert_mode 16w) uf uy)``,
    RW_TAC (srw_ss()) [user_simp_par_or_eqv_lem, preserve_relation_mmu_def]);


val user_simp_par_or_and_rel_lem = store_thm(
    "user_simp_par_or_and_rel_lem",
    ``!E A P elsecomp uf uy.
      (preserve_relation_mmu
       (((current_mode_is_user_or_system <|proc := 0|> ||| P) >>=
             (λ(is_user_or_system_mode,otherparam).
                if is_user_or_system_mode \/ (A /\ otherparam) then
                  (errorT E: 'a M)
                else
                  elsecomp))) (assert_mode 16w) (assert_mode 16w) uf uy)
        = 
      (preserve_relation_mmu
       (((current_mode_is_user_or_system <|proc := 0|> ||| P)>>=
             (λ(is_user_or_system_mode,otherparam).
                (errorT E: 'a M)))) (assert_mode 16w) (assert_mode 16w) uf uy)``,
     RW_TAC (srw_ss()) [user_simp_par_or_and_lem, preserve_relation_mmu_def]);



val priv_simp_preserves_help_comb_thm = prove_and_save_p_helper (``current_mode_is_priviledged <|proc := 0|> >>=
            (\current_mode_is_priviledged. take_undef_instr_exception <|proc:=0|>)``, "priv_simp_preserves_comb_help_thm");

val user_simp_preserves_help_thm = prove_and_save (``current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode. (errorT E))``, "user_simp_preserves_help_thm");



val priv_simp_preserves_comb_thm = store_thm(
    "priv_simp_preserves_comb_thm",
    ``!ifcomp.
      (preserve_relation_mmu
        (current_mode_is_priviledged <|proc:=0|> >>=
          (\current_mode_is_priviledged.
           if current_mode_is_priviledged then
             ifcomp
           else
             take_undef_instr_exception <|proc:=0|>)) (assert_mode 16w) (comb_mode 16w 27w)  priv_mode_constraints priv_mode_similar)``,
     RW_TAC (srw_ss()) [priv_simp_rel_lem, priv_simp_preserves_help_comb_thm]);



val user_simp_preserves_empty_thm = store_thm(
    "user_simp_preserves_empty_thm",
    ``!E elsecomp. (preserve_relation_mmu
       ((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                if is_user_or_system_mode then
                  errorT E
                else
                  elsecomp))) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim)``,
     RW_TAC (srw_ss()) [user_simp_rel_lem, user_simp_preserves_help_thm]);

val user_simp_preserves_thm = (MATCH_MP extras_lem2 (SPEC_ALL user_simp_preserves_empty_thm));

val user_simp_or_preserves_empty_thm = store_thm(
    "user_simp_or_preserves_empty_thm",
    ``!E A elsecomp. (preserve_relation_mmu
       ((current_mode_is_user_or_system <|proc := 0|> >>=
             (λis_user_or_system_mode.
                if is_user_or_system_mode \/ A then
                  errorT E
                else
                  elsecomp))) (assert_mode 16w) (assert_mode 16w) empty_unt empty_sim)``,
     RW_TAC (srw_ss()) [user_simp_or_rel_lem, user_simp_preserves_help_thm]);

val user_simp_or_preserves_thm = (MATCH_MP extras_lem2 (SPEC_ALL user_simp_or_preserves_empty_thm));


add_to_simplist user_simp_preserves_thm;
add_to_simplist user_simp_or_preserves_thm;
add_to_simplist priv_simp_preserves_comb_thm;


