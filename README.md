<!-- This repo is mainly about tools
that allow one to collect data sets from F\* builds,
notably from checked files.

To run:
 1. Build F\* with the `--record_options` flag.
    This tells F\* to record the options it used to check each definition
    in the checked file. This allows `fstar_insights` to preserve this in
    the data set.

    Typically, if you're building F\* itself, this would be `OTHERFLAGS='--record_options' make -jN`

 2. Make sure you have done `eval $(opam env)` and set the `FSTAR_HOME` environment variable.

 3. `make -C fstar_insights`

 4. `./ingest.py .../path/to/FStar` (or `./ingest.py .../path/to/everest`)


After all that, you can run `make harness-checked.json`
as a sanity check to see if the harness can verify extracted proofs.

This repo also provides `fstar_harness.py`, which is a harness to run F\*
against sample proofs collected from the dataset. -->

# Preliminaries

1. Make sure the [`helpers`](./helpers/) folder is present in this directory. Initially the release contains `helpers.zip` which needs to be extracted. Run `unzip helpers.zip` if `helpers` directory is not present.
2. Add [`helpers/bin`](./helpers/bin/) to your `PATH`, i.e., `export PATH=$(pwd)/helpers/bin:$PATH`.
3. Make sure `fstar.exe --version` works, and the output is `F* 2023.09.03~dev`.

# Preparing Evaluation Data
For evaluation, we need the entire example dictionary in the dataset. For evaluating generated F* definition(s) put them as a list of strings in the example disctionaries. 
Suppose the following is the example you are working with
```json
{
   "file_name": "FStar.Old.Endianness.fst",
   "name": "FStar.Old.Endianness.u64",
   ...
}
```
Then, you can add the generated F* definition(s) as follows
```json
{
   "file_name": "FStar.Old.Endianness.fst",
   "name": "FStar.Old.Endianness.u64",
   ...
   "generated_response": {
      "responses": [
         "let u64 = UInt64.t",
         "let u64 = UInt32.t",
         "let u64 = UInt16.t",
         ...
      ]
   }
}
```
Now you can pass `generated_response/responses` as the `solution_key` to the evaluation script. Note that the `solution_key` is recursively resolved split by `/`. For example, the `solution_key` `generated_response/responses` will be resolved as `example['generated_response']['responses']`. The solutions could be a list of strings or a single string.


# Running Evaluation
To run the evaluation, you can use the following command
```bash
python evaluate.py \
   --input_files INPUT_FILES (could be multiple) \
   --dataset_dir $(pwd)/helpers/support_files \
   --solution_key SOLUTION_KEY (default is generated_response/responses) \
   --output_dir OUTPUT_DIR (optional) \
   --output OUTPUT_FILE (Only the name of the output file, optional)
```
The `evaluate.py` script will output the evaluation results in the `OUTPUT_DIR/OUTPUT_FILE` if `OUTPUT_DIR/` is provided, otherwise it will print the results on the console.