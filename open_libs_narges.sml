
load "armLib";
open armLib;

open arm_seq_monadTheory;
open arm_opsemTheory;
open arm_coretypesTheory;

use "hypervisor_fixed_constants.sml";
use "out/hypervisor_constants.sml";
use "out/hypervisor_values.sml";

use "my_tacs.sml";
use "play_on_words.sml";
use "mmu5.sml";

use "Theory/HypervisorModelScript.sml";
use "guests_and_mmu.sml";
use "hypervisor_invariants.sml";
 
(* low level user/switching lemma *)
(* use "verification/hol4/switching_lemma/low_level_user_switching_lemma.high"; *)

(* sml level lemmas including user/switching *)
use "verification/hol4/main_theorem_proof/untouched.sml";
use "verification/hol4/main_theorem_proof/relation_lemmas.sml";

(* proof of main theorem *)
use "outer_full_relation.sml";
use "verification/hol4/main_theorem_proof/outer_user_switching_super_lemmas.sml";
use "verification/hol4/main_theorem_proof/bisim_proof.sml";


(******** proof of privilaged constraints (Narges) *************)
use "prover/ARM_proof_tool_params_swithing.sml";
use "verification/hol4/switching_lemma/privilaged_mode_constraints.sml";

use "verification/hol4/switching_lemma/priv_mode_constraints_cpsr_flags_set_pc.sml";
use "verification/hol4/switching_lemma/privilaged_mode_LR_svc.sml";

use "verification/hol4/switching_lemma/privilaged_mode_bisimilar.sml";

use "prover/ARM_proof_tool_switching.v2.0.sml";
use "verification/hol4/switching_lemma/switching_lemma.sml";


