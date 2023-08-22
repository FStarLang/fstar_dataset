BM_HOME=../../..
FSTAR_ULIB=$(FSTAR_HOME)/ulib
ALL_JSON_IN_FILES=$(addsuffix .json, $(notdir $(wildcard $(FSTAR_ULIB)/*.fst $(FSTAR_ULIB)/*.fsti)))
ALL_JSON_OUT_FILES=$(addsuffix .out, $(filter-out interact_with_fstar.config.json, $(wildcard *.json)))

all: $(addprefix out/, $(ALL_JSON_OUT_FILES))

defs_and_premises: $(ALL_JSON_IN_FILES)

out/%.json.out: %.json out
	python3 $(BM_HOME)/InteractWithFStar.py $< $(PWD)/out $<.out

%.json: $(FSTAR_ULIB)/%
	../../ocaml/bin/fstar_insights.exe --include $(FSTAR_ULIB)/.cache --include $(FSTAR_ULIB)  --all_defs_and_premises $(notdir $<) > $@

out:
	mkdir -p out
