../../utils/scripts/baputils.py --preprocess ../out/indirect/boot_mem_init_part3_end.il ../out/boot_mem_init_part3.il
/opt/trunk/utils/topredicate -validity -il ../out/boot_mem_init_part3.il -post goal -stp-out ../out/boot_mem_init_part3.stp
stp ../out/boot_mem_init_part3.stp
