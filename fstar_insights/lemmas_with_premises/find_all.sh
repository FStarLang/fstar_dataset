#!/usr/bin/bash

FSTAR_ULIB=$FSTAR_HOME/ulib
TARGET_DIR=ulib_json.0926
mkdir -p $TARGET_DIR

for file in `ls $FSTAR_ULIB/*.fst $FSTAR_ULIB/*.fsti`; do
    basefile=`basename $file`
    echo $basefile
    ../ocaml/bin/fstar_insights.exe --include $FSTAR_ULIB/.cache --include $FSTAR_ULIB --all_defs_and_premises $basefile > $TARGET_DIR/$basefile.json
done

#find . -type f -empty | xargs rm
