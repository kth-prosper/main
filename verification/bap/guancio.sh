#!/bin/sh
../../utils/scripts/baputils.py --preprocess test/guanciotest.il ../out/guanciotest.il
#/opt/trunk/utils/topredicate -validity -il ../../out/guanciotest.il -post postcondition -o ../../out/guanciotest.post.old.il

#/opt/trunk/utils/guancio -validity -il ../../out/guanciotest.il -post postcondition -o ../../out/guanciotest.post.il
/opt/trunk/utils/guancio -validity -il ../out/guanciotest.il -post goal -stp-out ../out/guanciotest.stp -o ../out/guanciores.il
stp ../out/guanciotest.stp