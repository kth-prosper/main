../../utils/scripts/baputils.py --preprocess ../out/indirect/boot_mem_init_part2_end.il ../out/boot_mem_init_part2.il
/opt/trunk/utils/guancio -validity -il ../out/boot_mem_init_part2.il -post goal -stp-out ../out/boot_mem_init_part2.stp > /dev/null
stp ../out/boot_mem_init_part2.stp
