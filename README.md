* This repo is mainly about tools that allow one to collect data sets
  from F* builds, notably from checked files.

  - This is mainly in fstar_insights and QueryCheckedFiles.fst

* It also provides InteractWithFStar.py, which is a harness to run F*
  against sample proofs collected from the dataset

* Note, when building an F* project, pass the `--record_options` flag
  to F* to have it record the options it used to check each definition
  in the checked file. This allows fstar_insights to preserve this in
  the data set.

  Typically, if you're building F* itself, this would be

  OTHERFLAGS='--record_options' make -jN

* To run this on ulib:
   * build F*
   * run make in fstar_insights
   * in lemmas_with_premises/ulib_json, use the Makefile to
     - make defs_and_premises (to collect all the json files in the ulib dataset)
     - make all (to replay all the proofs using InteractWithFStar.py)
