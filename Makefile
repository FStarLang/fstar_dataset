ALL_JSON_IN_FILES=$(addsuffix .json, $(wildcard dataset/*.fst dataset/*.fsti))

.PHONY: all extract harness-check clean

all:

extract: $(ALL_JSON_IN_FILES)

dataset/%.json: dataset/% dataset/%.checked
	./fstar_insights/ocaml/bin/fstar_insights.exe --include dataset --all_defs_and_premises $* > $@

harness-checked.json: $(ALL_JSON_IN_FILES)
	./fstar_harness.py dataset $+ >$@ || $(RM) $@

clean:
	$(RM) -r dataset harness-checked
