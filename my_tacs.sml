val UNDISCH_MATCH_TAC = fn MATCH => (PAT_ASSUM MATCH (fn th => (MP_TAC th)));
val UNDISCH_ALL_TAC = (REPEAT (UNDISCH_MATCH_TAC ``X``));

val SPEC_ASSUM_TAC = fn (MATCH, SLIST) => (REPEAT (PAT_ASSUM MATCH (fn th => ASSUME_TAC (SPECL SLIST th))));
val SPEC_AND_KEEP_ASSUM_TAC = fn (MATCH, SLIST) => (PAT_ASSUM MATCH (fn th => ASSUME_TAC th THEN ASSUME_TAC (SPECL SLIST th)));


val THROW_AWAY_TAC = fn MATCH => (REPEAT (PAT_ASSUM MATCH (fn th => IMP_RES_TAC th)));
val THROW_ONE_AWAY_TAC = fn MATCH => (PAT_ASSUM MATCH (fn th => IMP_RES_TAC th));
val THROW_AWAY_IMPLICATIONS_TAC = (REPEAT (WEAKEN_TAC is_imp));


val ASSERT_ASSUM_TAC = fn MATCH => (PAT_ASSUM MATCH (fn th => ASSUME_TAC th));


val PROTECTED_RW_TAC = fn MATCH => (PAT_ASSUM MATCH (fn th => (RW_TAC (srw_ss()) [] THEN ASSUME_TAC th)));

val PROTECTED_OR_RW_TAC = fn RWLIST => (PAT_ASSUM ``X \/ Y`` (fn th => (RW_TAC (srw_ss()) RWLIST THEN ASSUME_TAC th))) ORELSE (RW_TAC (srw_ss()) RWLIST);

val PROTECTED_OR_SIMP_TAC = fn RWLIST => (PAT_ASSUM ``X \/ Y`` (fn th => (FULL_SIMP_TAC (srw_ss()) RWLIST THEN ASSUME_TAC th))) ORELSE (FULL_SIMP_TAC (srw_ss()) RWLIST);

val CONJ_ASSUM_TAC = (REPEAT (PAT_ASSUM ``A /\ B`` (fn th => ASSUME_TAC (CONJUNCT1 th) THEN ASSUME_TAC (CONJUNCT2 th))));


val FORCE_REWRITE_TAC = (fn thm =>
                             let val (_, trm) = dest_thm (SPEC_ALL thm)
                                 val COMB (ab, c) = dest_term trm
                                 val COMB (a, b) = dest_term ab
                             in SUBGOAL_THEN c (fn sgl => ASSUME_TAC thm  THEN ASSUME_TAC sgl THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [])
                             end);


val FORCE_REV_REWRITE_TAC = (fn thm =>
                             let val (_, trm) = dest_thm (SPEC_ALL thm)
                                 val COMB (ab, c) = dest_term trm
                                 val COMB (a, b) = dest_term ab
                             in SUBGOAL_THEN b (fn sgl => ASSUME_TAC thm  THEN ASSUME_TAC sgl THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [])
                             end);

