new_constant ("guest1_min_adr", ``:word32``);
new_constant ("guest1_max_adr", ``:word32``);
new_constant ("guest2_min_adr", ``:word32``);
new_constant ("guest2_max_adr", ``:word32``);

new_constant ("guest1_msg_handler_adr", ``:word32``);
new_constant ("guest2_msg_handler_adr", ``:word32``);

val guest1_min_adr_axiom =
    new_axiom("guest1_min_adr_axiom",
	      ``guest1_min_adr = 0x100000w``);
val guest1_max_adr_axiom =
    new_axiom("guest1_max_adr_axiom",
	      ``guest1_max_adr= 0x3FFFFFw``);
val guest2_min_adr_axiom =
    new_axiom("guest2_min_adr_axiom",
	      ``guest2_min_adr = 0x400000w``);
val guest2_max_adr_axiom =
    new_axiom("guest2_max_adr_axiom",
	      ``guest2_max_adr = 0x6FFFFFw``);


val guest1_msg_handler_adr_axiom =
    new_axiom("guest1_msg_handler_adr_axiom",
	      ``guest1_msg_handler_adr = 0x300000w``);
val guest2_msg_handler_adr_axiom =
    new_axiom("guest2_msg_handler_adr_axiom",
	      ``guest2_msg_handler_adr = 0x600000w``);

val hypervisor_guest_mem_axioms = [
guest1_min_adr_axiom,
guest1_max_adr_axiom,
guest2_min_adr_axiom,
guest2_max_adr_axiom];
