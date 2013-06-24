#!/bin/sh
# ../../utils/scripts/baputils.py --preprocess src/check_mem_init_body.il ../out/check_mem_init_body.il
# /opt/trunk/utils/guancio -validity -il ../out/check_mem_init_body.il -post goal -stp-out ../out/check_mem_init_body.stp -o ../out/check_mem_init_body.post.il
# stp ../out/check_mem_init_body.stp

# ../../utils/scripts/baputils.py --preprocess src/mem_init_1.il ../out/mem_init_1.il
# /opt/trunk/utils/guancio -validity -il ../out/mem_init_1.il -post goal -stp-out ../out/mem_init_1.stp -o ../out/mem_init_1.post.il
# stp ../out/mem_init_1.stp

../../utils/scripts/baputils.py --preprocess src/mem_init_end.il ../out/mem_init_end.il
/opt/trunk/utils/guancio -validity -il ../out/mem_init_end.il -post goal -stp-out ../out/mem_init_end.stp -o ../out/mem_init_end.post.il
stp ../out/mem_init_end.stp