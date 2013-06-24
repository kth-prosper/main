../../utils/scripts/baputils.py --preprocess src/from_hol/rcv.il ../out/from_hol/rcv.il
/opt/trunk/utils/topredicate -validity -il ../out/from_hol/rcv.il -post goal -stp-out ../out/from_hol/rcv.stp
stp ../out/from_hol/rcv.stp

# test to check the size of the condition
#/opt/trunk/utils/topredicate -validity -il ../out/from_hol/si_1.il -post postcondition -stp-out ../out/from_hol/si_1.wp.stp
#../../utils/scripts/baputils.py --preprocess src/from_hol/si_1.pre.il ../out/from_hol/si_1.tmp.pre.il
#/opt/trunk/utils/topredicate -validity -il ../out/from_hol/si_1.tmp.pre.il -post precondition -stp-out ../out/from_hol/si_1.tmp.pre.stp

# test with the other solver
#/opt/trunk/utils/topredicate -validity -il ../out/from_hol/si_1.il -post goal -solver yices -stp-out ../out/from_hol/si_1.yices
#/opt/trunk/utils/topredicate -validity -flanagansaxe -il ../out/from_hol/si_1.il -post goal -solver yices -stp-out ../out/from_hol/si_1.flanagansaxe.yices
#/NOBACKUP/workspaces/robertog/verification/yices-1.0.36/bin/yices -v 2 -e -st -smt < ../out/from_hol/si_1.yices


# test with the cvc solver
#/opt/trunk/utils/topredicate -validity -il ../out/from_hol/si_1.il -post goal -solver cvc3 -stp-out ../out/from_hol/si_1.cvc3
#/opt/trunk/utils/topredicate -validity -flanagansaxe -il ../out/from_hol/si_1.il -post goal -solver cvc3 -stp-out ../out/from_hol/si_1.flanagansaxe.cvc3
#/NOBACKUP/workspaces/robertog/cvc3-2.4.1-optimized-static/bin/cvc3 ../out/from_hol/si_1.cvc3



#/NOBACKUP/workspaces/robertog/verification/yices-1.0.36/bin/yices -v 2 -e -st -smt < ../out/from_hol/si_1.yices



# /opt/trunk/utils/topredicate -validity -flanagansaxe -il out/si_1.il -post goal -stp-out out/si_1.stp  -solver yices
# yices -v 2 -e -st -smt < out/si_1.stp

# ./baputils.py --preprocess src/mem_init.loop.2.il out/mem_init.loop.2.il
# /opt/trunk/utils/topredicate -validity -flanagansaxe -il out/mem_init.loop.2.il -post goal -stp-out out/mem_init.loop.2.stp -solver yices  > out/mem_init.loop.2.post.il
# # ./baputils.py --change-stp out/mem_init.loop.2.stp 
# # stp out/mem_init.loop.2.stp > out/mem_init.loop.2.stp.out
# # ./memory.py out/mem_init.loop.2.stp.out 0x000081E4 40
# yices -v 2 -e -st -smt < out/mem_init.loop.2.stp
