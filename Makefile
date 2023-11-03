ALL_JSON_IN_FILES=$(addsuffix .json, $(wildcard dataset/*.fst dataset/*.fsti))

.PHONY: all harness-check clean

all: harness-checked.json

harness-checked.json: $(ALL_JSON_IN_FILES)
	./fstar_harness.py dataset $+ >$@ || $(RM) $@

clean:
	$(RM) -r dataset harness-checked.json
