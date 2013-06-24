./baputils.py --preprocess src/si_1.il out/si_1.il
/opt/trunk/utils/topredicate -validity -il out/si_1.il -post goal -stp-out out/si_1.stp
stp out/si_1.stp
# /opt/trunk/utils/topredicate -validity -flanagansaxe -il out/si_1.il -post goal -stp-out out/si_1.stp  -solver yices
# yices -v 2 -e -st -smt < out/si_1.stp

# ./baputils.py --preprocess src/mem_init.loop.2.il out/mem_init.loop.2.il
# /opt/trunk/utils/topredicate -validity -flanagansaxe -il out/mem_init.loop.2.il -post goal -stp-out out/mem_init.loop.2.stp -solver yices  > out/mem_init.loop.2.post.il
# # ./baputils.py --change-stp out/mem_init.loop.2.stp 
# # stp out/mem_init.loop.2.stp > out/mem_init.loop.2.stp.out
# # ./memory.py out/mem_init.loop.2.stp.out 0x000081E4 40
# yices -v 2 -e -st -smt < out/mem_init.loop.2.stp
