;
use "/NOBACKUP/workspaces/oschwarz/holmodel/verification/hol4/user_lemma/oschwarzconf.sml";
use "open_libs.sml";
use "verification/hol4/user_lemma/load.sml";

(* to cut a corner : *)

val mode_mix_def = Define `mode_mix = (\s. (ARM_MODE s = 16w) \/ (ARM_MODE s = 27w) \/ (ARM_MODE s = 23w) \/ (ARM_MODE s = 19w))`;


val mmu_arm_next_comb_thm = save_thm("mmu_arm_next_comb_thm",
                          new_axiom("mmu_arm_next_comb_thmX",
                                    ``(irpt <> HW_Reset) ==> preserve_relation_mmu (mmu_arm_next irpt) (assert_mode 16w) mode_mix priv_mode_constraints_v3 priv_mode_similar``));


val similarity_implies_equal_mode_thm = store_thm(
    "similarity_implies_equal_mode_thm", 
    ``! g s1 s2. (similar g s1 s2) ==> (ARM_MODE s1 = ARM_MODE s2)``,
    EVAL_TAC
      THEN RW_TAC (srw_ss()) []
      THEN SPEC_ASSUM_TAC (``!(ii:iiid). X``, [``<|proc:=0|>``])
      THEN FULL_SIMP_TAC (srw_ss()) []);


