#!/usr/bin/bash

FSTAR_ULIB=$FSTAR_HOME/ulib

for file in `ls $FSTAR_ULIB/FStar.BV.fst`; do
    basefile=`basename $file`
    echo $basefile
    ../ocaml/bin/fstar_insights.exe --include $FSTAR_ULIB/.cache --all_defs_and_premises $basefile > $basefile.all_defs_and_premises.json
done

#find . -type f -empty | xargs rm
