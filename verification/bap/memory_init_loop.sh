../../utils/scripts/baputils.py --preprocess src/from_hol/memory_init_loop.il ../out/memory_init_loop.il

/opt/bap-0.7-guancio/utils/topredicate2 -validity -il ../out/memory_init_loop.il -post goal -stp-out ../out/memory_init_loop.stp

/opt/stp-src/bin/stp ../out/memory_init_loop.stp


