This directory contains the sources of the fstar_insights tool,
used to process checked files and emit the JSON files used in F* dataset.

It is built against the version of F* in the submodule projects/FStar

To build this project, you must first:

* In the root directory, run

  $ ./projects/build.sh build_fstar
  
* Then, run `make` in this directory

  This will first create JsonHelper.fst

You can also interactively develop QueryCheckedFile.fst in VSCode or emacs, 
but you must make sure that JsonHelper.fst exists first.
