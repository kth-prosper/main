../../utils/scripts/baputils.py --preprocess ../out/indirect/cswitch_end.il ../out/cswitch.il
/opt/trunk/utils/topredicate -validity -il ../out/cswitch.il -post goal -stp-out ../out/cswitch.stp
stp ../out/cswitch.stp
