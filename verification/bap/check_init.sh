#!/bin/sh

# ./baputils.py --preprocess src/mem_init_manual.il out/mem_init_manual.il
# iltrans -il out/mem_init_manual.il -to-cfg -to-ssa -pp-ssa out/mem_init_manual.dot
# dot -Tpdf out/mem_init_manual.dot -o out/mem_init_manual.pdf


# ./baputils.py --preprocess test/mem_loop.2.il out/mem_loop.2.il
# topredicate -il out/mem_loop.2.il -post postcondition

# ./baputils.py --preprocess test/mem_loop.2.il out/mem_loop.2.il
# topredicate -il out/mem_loop.2.il -post goal -stp-out out/mem_loop.2.stp
# ./baputils.py --change-stp out/mem_loop.2.stp
# stp out/mem_loop.2.stp  > out/mem_loop.2.stp.out
# ./memory.py out/mem_loop.2.stp.out 0x00000000 20


# ./baputils.py --preprocess src/mem_init.loop.2.il out/mem_init.loop.2.il
# topredicate -il out/mem_init.loop.2.il -post goal -stp-out out/mem_init.loop.2.stp > /tmp/post.il
# ./baputils.py --change-stp out/mem_init.loop.2.stp
# stp out/mem_loop.2.stp  > out/mem_init.loop.2.stp.out

# check the loop (I'm working here)
# ./baputils.py --preprocess src/mem_init.loop.2.il out/mem_init.loop.2.il
# # topredicate -dwp -il out/mem_init.loop.2.il -post postcondition  > out/mem_init.loop.2.post.il
# # topredicate -q -il out/mem_init.loop.2.il -post goal -stp-out out/mem_init.loop.2.stp 
# topredicate -il out/mem_init.loop.2.il -post goal -stp-out out/mem_init.loop.2.stp  > out/mem_init.loop.2.post.il


#topredicate -il out/mem_init.loop.2.il -post precondition -stp-out out/mem_init.loop.2.pre.stp  > out/mem_init.loop.2.pre.il
# ./baputils.py --preprocess src/mem_init.loop.2.pre.il out/mem_init.loop.2.pre.il
# topredicate -il out/mem_init.loop.2.pre.il -post precondition -stp-out out/mem_init.loop.2.pre.stp


# MMMMMMMMM BIG
./baputils.py --preprocess src/mem_init.loop.2.il out/mem_init.loop.2.il
/opt/trunk/utils/topredicate -validity -flanagansaxe -il out/mem_init.loop.2.il -post goal -stp-out out/mem_init.loop.2.stp -solver yices  > out/mem_init.loop.2.post.il
# ./baputils.py --change-stp out/mem_init.loop.2.stp 
# stp out/mem_init.loop.2.stp > out/mem_init.loop.2.stp.out
# ./memory.py out/mem_init.loop.2.stp.out 0x000081E4 40
yices -v 2 -e -st -smt < out/mem_init.loop.2.stp

#./baputils.py --preprocess src/mem_init.loop.1.il out/mem_init.loop.1.il
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