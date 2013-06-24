#!/bin/sh
./baputils.py --preprocess src/mem_init.loop.2.il out/mem_init.loop.2.il
/opt/trunk/utils/topredicate -validity -flanagansaxe -il out/mem_init.loop.2.il -post postcondition -o out/mem_init.loop.2.post.il


./baputils.py --preprocess src/mem_init.loop.1.il out/mem_init.loop.1.il
/opt/trunk/utils/topredicate -noopt -validity -il out/mem_init.loop.1.il -post goal -stp-out out/mem_init.loop.1.stp  -solver yices > out/mem_init.loop.1.pre.il
yices -v 2 -e -st -smt < out/mem_init.loop.1.stp
#topredicate -il out/mem_init.loop.1.il -post postcondition -stp-out out/mem_init.loop.1.stp
# stp out/mem_init.loop.1.stp  > out/mem_init.loop.1.stp.out

# generate control flow of the loop body
# iltrans -il out/mem_init.loop.2.il -to-cfg -to-ssa -pp-ssa out/mem_init_manual.dot
# dot -Tpdf out/mem_init_manual.dot -o out/mem_init_manual.pdf

#./baputils.py --preprocess test/mem_init_size.il out/mem_init_size.il
#topredicate -il out/mem_init_size.il -post postcondition  -stp-out out/mem_init_size.stp  > out/mem_init_size.post.il
#./baputils.py --change-stp out/mem_init_size.stp
#/opt/trunk/utils/topredicate -validity -flanagansaxe -il out/mem_init_size.il -post goal  -stp-out out/mem_init_size.stp -solver yices  > out/mem_init_size.post.il
#yices -e -st -smt < out/mem_init_size.stp

# /opt/trunk/utils/topredicate -validity  -il out/mem_init_size.il -post goal  -stp-out out/mem_init_size.stp -solver stp  > out/mem_init_size.post.il
# stp out/mem_init_size.stp


#./baputils.py --change-stp out/mem_init_size.stp
#stp out/mem_init_size.stp 

# topredicate -dwp1 -il test/aaa_size.il -post "R0:u32>1:u32"  -stp-out out/aaa_size.stp
#/opt/trunk/utils/topredicate -validity  -il test/aaa_size.il -post "R0:u32>1:u32"  -solve -solver yices -stp-out out/aaa_size.stp
#./baputils.py --change-stp out/aaa_size.stp
# stp out/aaa_size.stp 