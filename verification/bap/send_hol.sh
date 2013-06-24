../../utils/scripts/baputils.py --preprocess ../out/indirect/send_end.il ../out/send.il
/opt/trunk/utils/topredicate -validity -il ../out/send.il -post goal -stp-out ../out/send.stp
stp ../out/send.stp
