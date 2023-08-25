#!/usr/bin/bash

FSTAR_ULIB=$FSTAR_HOME/ulib

for file in `ls $FSTAR_ULIB/*.fst $FSTAR_ULIB/*.fsti`; do
    basefile=`basename $file`
    echo $basefile
    ../ocaml/bin/fstar_insights.exe --include $FSTAR_ULIB/.cache --include $FSTAR_ULIB --all_defs_and_premises $basefile > ulib_json/$basefile.json
done

#find . -type f -empty | xargs rm
