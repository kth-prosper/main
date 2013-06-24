../../utils/scripts/baputils.py --preprocess ../out/indirect/prefetch_end.il ../out/prefetch.il
/opt/trunk/utils/topredicate -validity -il ../out/prefetch.il -post goal -stp-out ../out/prefetch.stp
stp ../out/prefetch.stp
