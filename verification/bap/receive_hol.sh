../../utils/scripts/baputils.py --preprocess ../out/indirect/receive_end.il ../out/receive.il
/opt/trunk/utils/topredicate -validity -il ../out/receive.il -post goal -stp-out ../out/receive.stp
stp ../out/receive.stp
