This repo is mainly about tools
that allow one to collect data sets from F\* builds,
notably from checked files.

To run:
 1. Build F\* with the `--record_options` flag.
    This tells F\* to record the options it used to check each definition
    in the checked file. This allows `fstar_insights` to preserve this in
    the data set.

    Typically, if you're building F\* itself, this would be `OTHERFLAGS='--record_options' make -jN`

 2. Make sure you have done `eval $(opam env)` and set the `FSTAR_HOME` environment variable.

 3. `./ingest.py .../path/to/FStar`

 4. `make -C fstar_insights`

 5. `make extract -j$(nproc)`

<!--
explain where the files are stored and what info they contain
-->

After all that, you can run `make harness-check -j$(nproc)`
as a sanity check to see if the harness can verify extracted proofs.

This repo also provides `InteractWithFStar.py, which is a harness to run F*
against sample proofs collected from the dataset
