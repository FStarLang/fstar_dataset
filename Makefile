ALL_JSON_IN_FILES=$(addsuffix .json, $(wildcard dataset/*.fst dataset/*.fsti))
ALL_JSON_OUT_FILES=$(addprefix harness-checked/, $(ALL_JSON_IN_FILES:dataset/%=%))

.PHONY: all extract harness-check clean

all:

extract: $(ALL_JSON_IN_FILES)

dataset/%.json: dataset/% dataset/%.checked
	./fstar_insights/ocaml/bin/fstar_insights.exe --include dataset --all_defs_and_premises $* > $@

harness-check: $(ALL_JSON_OUT_FILES)

harness-checked/%.json: dataset/%.json
	mkdir -p harness-checked
	./fstar_harness.py dataset <$< >$@ || $(RM) $@

clean:
	$(RM) -r dataset harness-checked
