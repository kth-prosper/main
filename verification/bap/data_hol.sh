../../utils/scripts/baputils.py --preprocess ../out/indirect/data_end.il ../out/data.il
/opt/trunk/utils/topredicate -validity -il ../out/data.il -post goal -stp-out ../out/data.stp
stp ../out/data.stp
