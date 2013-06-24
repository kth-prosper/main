../../utils/scripts/baputils.py --preprocess ../out/indirect/release_end.il ../out/release.il
/opt/trunk/utils/topredicate -validity -il ../out/release.il -post goal -stp-out ../out/release.stp
stp ../out/release.stp
