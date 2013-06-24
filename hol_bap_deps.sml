(* Remember to use the $userconf.sml to set-up the loadPath *)
load "arm_evalLib";
open arm_evalLib;

use "out/hypervisor_constants.sml";

use "Theory/HypervisorModelScript.sml";
(* load "HypervisorModelTheory"; *)
(* open HypervisorModelTheory; *)
new_constant("access_violation", ``:arm_state -> bool``);
use "mmu5.sml";
use "relation_lemmas.sml";
