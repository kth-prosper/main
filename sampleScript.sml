open HolKernel boolLib Parse bossLib

val _ = new_theory "sample";

new_constant ("roberto", ``:bool``);

val _ = export_theory();
