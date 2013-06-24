
load "armLib";
open armLib;

(* open IsolationVerifTheory; *)
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
use "verification/hol4/switching_lemma/low_level_user_switching_lemma.sml";

(* high level lemmas including user/switching *)
use "verification/hol4/main_theorem_proof/relation_lemmas.sml";
