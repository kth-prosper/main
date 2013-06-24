#!/bin/sh

./baputils.py --preprocess src/manual_mem_lookup.3.il out/manual_mem_lookup.3.il
topredicate -il out/manual_mem_lookup.3.il -post goal -stp-out out/manual_mem_lookup.3.stp
./baputils.py --change-stp out/manual_mem_lookup.3.stp
stp out/manual_mem_lookup.3.stp


./baputils.py --preprocess src/manual_mem_lookup.2.il out/manual_mem_lookup.2.il
topredicate -il out/manual_mem_lookup.2.il -post goal -stp-out out/manual_mem_lookup.2.stp
./baputils.py --change-stp out/manual_mem_lookup.2.stp
stp out/manual_mem_lookup.2.stp
# stp out/manual_mem_lookup.2.stp > out/manual_mem_lookup.2.stp.out
# ./memory.py out/manual_mem_lookup.2.stp.out 0x000081e4 40

./baputils.py --preprocess src/manual_mem_lookup.1.il out/manual_mem_lookup.1.il
topredicate -il out/manual_mem_lookup.1.il -post goal -stp-out out/manual_mem_lookup.1.stp
./baputils.py --change-stp out/manual_mem_lookup.1.stp
stp out/manual_mem_lookup.1.stp

# ./baputils.py --preprocess test/testBcc.il out/testBcc.il
# topredicate -il out/testBcc.il -post goal -stp-out out/testBcc.stp
# ./baputils.py --change-stp out/testBcc.stp
# stp out/testBcc.stp
