load "blastLib";


(* independent of concrete addresses *)

val inequal_by_inequalities_gt_lem = blastLib.BBLAST_PROVE ``!(x:word32) (a:word32) (b:word32). (a > x) /\  (b <= x) ==> (a <> b)``;

val inequal_by_inequalities_lt_lem = blastLib.BBLAST_PROVE ``!(x:word32) (a:word32) (b:word32). (a < x) /\  (b >= x) ==> (a <> b)``;

val inequal_by_inequalities_gtu_lem = blastLib.BBLAST_PROVE ``!(x:word32) (a:word32) (b:word32). (a >+ x) /\  (b <=+ x) ==> (a <> b)``;

val inequal_by_inequalities_ltu_lem = blastLib.BBLAST_PROVE ``!(x:word32) (a:word32) (b:word32). (a <+ x) /\  (b >=+ x) ==> (a <> b)``;



val inequal_by_inequalities = 
(CONJ (SPEC ``guest1_min_adr:word32`` inequal_by_inequalities_gtu_lem)
(CONJ (SPEC ``guest1_max_adr:word32`` inequal_by_inequalities_gtu_lem)
(CONJ (SPEC ``guest1_min_adr:word32`` inequal_by_inequalities_ltu_lem)
(CONJ (SPEC ``guest1_max_adr:word32`` inequal_by_inequalities_ltu_lem)
(CONJ (SPEC ``guest2_min_adr:word32`` inequal_by_inequalities_gtu_lem) 
(CONJ (SPEC ``guest2_max_adr:word32`` inequal_by_inequalities_gtu_lem)
(CONJ (SPEC ``guest2_min_adr:word32`` inequal_by_inequalities_ltu_lem) 
(CONJ (SPEC ``guest2_max_adr:word32`` inequal_by_inequalities_ltu_lem)
(CONJ (SPEC ``guest1_min_adr:word32`` inequal_by_inequalities_gt_lem)
(CONJ (SPEC ``guest1_max_adr:word32`` inequal_by_inequalities_gt_lem)
(CONJ (SPEC ``guest1_min_adr:word32`` inequal_by_inequalities_lt_lem)
(CONJ (SPEC ``guest1_max_adr:word32`` inequal_by_inequalities_lt_lem)
(CONJ (SPEC ``guest2_min_adr:word32`` inequal_by_inequalities_gt_lem) 
(CONJ (SPEC ``guest2_max_adr:word32`` inequal_by_inequalities_gt_lem)
(CONJ (SPEC ``guest2_min_adr:word32`` inequal_by_inequalities_lt_lem) 
      (SPEC ``guest2_max_adr:word32`` inequal_by_inequalities_lt_lem))))))))))))))));


val negated_inequalities_lem = blastLib.BBLAST_PROVE  ``!(x:word32) (y:word32).
                         ((~(y <= x)) ==> (y >  x))
                     /\  ((~(y <  x)) ==> (y >= x))
                     /\  ((~(y >  x)) ==> (y <= x))
                     /\  ((~(y >= x)) ==> (y <  x)) ``;

val negated_inequalities_unsigned_lem = blastLib.BBLAST_PROVE  ``!(x:word32) (y:word32).
                         ((~(y <=+ x)) ==> (y >+  x))
                     /\  ((~(y <+  x)) ==> (y >=+ x))
                     /\  ((~(y >+  x)) ==> (y <=+ x))
                     /\  ((~(y >=+ x)) ==> (y <+  x)) ``;


val negated_inequalities = 
 (CONJ (SPEC ``guest1_min_adr:word32`` negated_inequalities_unsigned_lem)
 (CONJ (SPEC ``guest1_max_adr:word32`` negated_inequalities_unsigned_lem)
 (CONJ (SPEC ``guest2_min_adr:word32`` negated_inequalities_unsigned_lem)
 (CONJ (SPEC ``guest2_max_adr:word32`` negated_inequalities_unsigned_lem)
 (CONJ (SPEC ``guest1_min_adr:word32`` negated_inequalities_lem)
 (CONJ (SPEC ``guest1_max_adr:word32`` negated_inequalities_lem)
 (CONJ (SPEC ``guest2_min_adr:word32`` negated_inequalities_lem)
       (SPEC ``guest2_max_adr:word32`` negated_inequalities_lem))))))));


val address_cases = blastLib.BBLAST_PROVE ``!(b:word32) (a:word32) (X:bool) (Y:bool).
(((a <= b) ==> X)  ==> (((a > b) \/ Y) ==> X)  ==> X) /\
(((a >= b) ==> X)  ==> ((Y \/ (a < b)) ==> X)  ==> X) /\
(((a <=+ b) ==> X)  ==> (((a >+ b) \/ Y) ==> X)  ==> X) /\
(((a >=+ b) ==> X)  ==> ((Y \/ (a <+ b)) ==> X)  ==> X)``;



val negated_and_or =  blastLib.BBLAST_PROVE
``!(a:word32).
((~(a > guest2_max_adr ∨ a < guest2_min_adr))  =  (a <= guest2_max_adr /\ a >= guest2_min_adr)) /\
((~(a ≤ guest1_max_adr ∧ a ≥ guest1_min_adr))  =  (a >  guest1_max_adr \/ a <  guest1_min_adr)) /\
((~(a > guest1_max_adr ∨ a < guest1_min_adr))  =  (a <= guest1_max_adr /\ a >= guest1_min_adr)) /\
((~(a ≤ guest2_max_adr ∧ a ≥ guest2_min_adr))  =  (a >  guest2_max_adr \/ a <  guest2_min_adr)) /\
((~(a > guest2_max_adr ∨ a < guest1_min_adr))  =  (a <= guest2_max_adr /\ a >= guest1_min_adr)) /\
((~(a >+ guest2_max_adr ∨ a <+ guest2_min_adr))  =  (a <=+ guest2_max_adr /\ a >=+ guest2_min_adr)) /\
((~(a <=+ guest1_max_adr ∧ a >=+ guest1_min_adr))  =  (a >+  guest1_max_adr \/ a <+  guest1_min_adr)) /\
((~(a >+ guest1_max_adr ∨ a <+ guest1_min_adr))  =  (a <=+ guest1_max_adr /\ a >=+ guest1_min_adr)) /\
((~(a <=+ guest2_max_adr ∧ a >=+ guest2_min_adr))  =  (a >+  guest2_max_adr \/ a <+  guest2_min_adr)) /\
((~(a >+ guest2_max_adr ∨ a <+ guest1_min_adr))  =  (a <=+ guest2_max_adr /\ a >=+ guest1_min_adr)) /\
((~(a > 0x2FFFFFw ∨ a < 0x200000w))  =  (a <= 0x2FFFFFw /\ a >= 0x200000w)) /\
((~(a ≤ 0x1FFFFFw ∧ a ≥ 0x100000w))  =  (a >  0x1FFFFFw \/ a <  0x100000w)) /\
((~(a > 0x1FFFFFw ∨ a < 0x100000w))  =  (a <= 0x1FFFFFw /\ a >= 0x100000w)) /\
((~(a ≤ 0x2FFFFFw ∧ a ≥ 0x200000w))  =  (a >  0x2FFFFFw \/ a <  0x200000w)) /\
((~(a > 0x2FFFFFw ∨ a < 0x100000w))  =  (a <= 0x2FFFFFw /\ a >= 0x100000w))``;



(* address border *)

val address_border_concrete = blastLib.BBLAST_PROVE ``!(a:word32). (a ≤ 0x1FFFFFw \/ a ≥ 0x200000w) /\ (a ≤ 0x3FFFFFw \/ a ≥ 0x400000w) /\ (a <=+ 0x3FFFFFw \/ a >=+ 0x400000w)``;

val address_border = store_thm(
    "address_border",
    ``!(a:word32). (a <=+ guest1_max_adr \/ a >=+ guest2_min_adr)``,
    FULL_SIMP_TAC (srw_ss()) [address_border_concrete, guest1_max_adr_axiom, guest2_min_adr_axiom]);


(* transitivity for all <, <=, >, >= *)
val address_trans = store_thm(
    "address_trans",
    ``!(x:word32).
((x <+  guest1_min_adr) ==> (x <=+ guest1_min_adr)) /\
((x <+  guest1_min_adr) ==> (x <+  guest1_max_adr)) /\
((x <+  guest1_min_adr) ==> (x <=+ guest1_max_adr)) /\
((x <+  guest1_min_adr) ==> (x <+  guest2_min_adr)) /\
((x <+  guest1_min_adr) ==> (x <=+ guest2_min_adr)) /\
((x <+  guest1_min_adr) ==> (x <+  guest2_max_adr)) /\
((x <+  guest1_min_adr) ==> (x <=+ guest2_max_adr)) /\
((x <=+ guest1_min_adr) ==> (x <+  guest1_max_adr)) /\
((x <=+ guest1_min_adr) ==> (x <=+ guest1_max_adr)) /\
((x <=+ guest1_min_adr) ==> (x <+  guest2_min_adr)) /\
((x <=+ guest1_min_adr) ==> (x <=+ guest2_min_adr)) /\
((x <=+ guest1_min_adr) ==> (x <+  guest2_max_adr)) /\
((x <=+ guest1_min_adr) ==> (x <=+ guest2_max_adr)) /\
((x <+  guest1_max_adr) ==> (x <=+ guest1_max_adr)) /\
((x <+  guest1_max_adr) ==> (x <+  guest2_min_adr)) /\
((x <+  guest1_max_adr) ==> (x <=+ guest2_min_adr)) /\
((x <+  guest1_max_adr) ==> (x <+  guest2_max_adr)) /\
((x <+  guest1_max_adr) ==> (x <=+ guest2_max_adr)) /\
((x <=+ guest1_max_adr) ==> (x <+  guest2_min_adr)) /\
((x <=+ guest1_max_adr) ==> (x <=+ guest2_min_adr)) /\
((x <=+ guest1_max_adr) ==> (x <+  guest2_max_adr)) /\
((x <=+ guest1_max_adr) ==> (x <=+ guest2_max_adr)) /\
((x <+  guest2_min_adr) ==> (x <=+ guest1_max_adr)) /\
((x <+  guest2_min_adr) ==> (x <=+ guest2_min_adr)) /\
((x <+  guest2_min_adr) ==> (x <+  guest2_max_adr)) /\
((x <+  guest2_min_adr) ==> (x <=+ guest2_max_adr)) /\
((x <=+ guest2_min_adr) ==> (x <+  guest2_max_adr)) /\
((x <=+ guest2_min_adr) ==> (x <=+ guest2_max_adr)) /\
((x <+  guest2_max_adr) ==> (x <=+ guest2_max_adr)) /\
((x >+  guest2_max_adr) ==> (x >=+ guest2_max_adr)) /\
((x >+  guest2_max_adr) ==> (x >+  guest2_min_adr)) /\
((x >+  guest2_max_adr) ==> (x >=+ guest2_min_adr)) /\
((x >+  guest2_max_adr) ==> (x >+  guest1_max_adr)) /\
((x >+  guest2_max_adr) ==> (x >=+ guest1_max_adr)) /\
((x >+  guest2_max_adr) ==> (x >+  guest1_min_adr)) /\
((x >+  guest2_max_adr) ==> (x >=+ guest1_min_adr)) /\
((x >=+ guest2_max_adr) ==> (x >+  guest2_min_adr)) /\
((x >=+ guest2_max_adr) ==> (x >=+ guest2_min_adr)) /\
((x >=+ guest2_max_adr) ==> (x >+  guest1_max_adr)) /\
((x >=+ guest2_max_adr) ==> (x >=+ guest1_max_adr)) /\
((x >=+ guest2_max_adr) ==> (x >+  guest1_min_adr)) /\
((x >=+ guest2_max_adr) ==> (x >=+ guest1_min_adr)) /\
((x >+  guest2_min_adr) ==> (x >=+ guest2_min_adr)) /\
((x >+  guest2_min_adr) ==> (x >+  guest1_max_adr)) /\
((x >+  guest2_min_adr) ==> (x >=+ guest1_max_adr)) /\
((x >+  guest2_min_adr) ==> (x >+  guest1_min_adr)) /\
((x >+  guest2_min_adr) ==> (x >=+ guest1_min_adr)) /\
((x >=+ guest2_min_adr) ==> (x >+  guest1_max_adr)) /\
((x >=+ guest2_min_adr) ==> (x >=+ guest1_max_adr)) /\
((x >=+ guest2_min_adr) ==> (x >+  guest1_min_adr)) /\
((x >=+ guest2_min_adr) ==> (x >=+ guest1_min_adr)) /\
((x >+  guest1_max_adr) ==> (x >=+ guest1_max_adr)) /\
((x >+  guest1_max_adr) ==> (x >+  guest1_min_adr)) /\
((x >+  guest1_max_adr) ==> (x >=+ guest1_min_adr)) /\
((x >=+ guest1_max_adr) ==> (x >+  guest1_min_adr)) /\
((x >=+ guest1_max_adr) ==> (x >=+ guest1_min_adr)) /\
((x >+  guest1_min_adr) ==> (x >=+ guest1_min_adr))``,
FULL_SIMP_TAC (srw_ss()) [guest1_min_adr_axiom, guest1_max_adr_axiom, guest2_min_adr_axiom, guest2_max_adr_axiom] THEN blastLib.BBLAST_TAC);


val address_complete = store_thm(
    "address_complete",
    ``!(add:word32). (add <=+ guest1_max_adr ∧ add >=+ guest1_min_adr) \/ 
                     (add <=+ guest2_max_adr ∧ add >=+ guest2_min_adr) \/
                     (add >+ guest2_max_adr ∨ add <+ guest1_min_adr)``,
    FULL_SIMP_TAC (srw_ss()) [guest1_min_adr_axiom, guest1_max_adr_axiom, guest2_min_adr_axiom, guest2_max_adr_axiom] THEN blastLib.BBLAST_TAC);




