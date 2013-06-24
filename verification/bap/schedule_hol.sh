../../utils/scripts/baputils.py --preprocess ../out/indirect/schedule_end.il ../out/schedule.il
/opt/trunk/utils/topredicate -validity -il ../out/schedule.il -post goal -stp-out ../out/schedule.stp
stp ../out/schedule.stp
