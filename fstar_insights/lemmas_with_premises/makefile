.PHONY: find_all build build_raw_dataset build_raw_dataset_from_gzip upload

zip:
	tar -czv -f dataset.tar.gz ./dataset
upload:
	***REMOVED***
	***REMOVED***

find_all: build
	mkdir -p dataset/
	find ./raw_dataset -type f -name "*.fst" | parallel  -j8 -replace='{}' '../ocaml/bin/fstar_insights.exe --include ./raw_dataset --include ./ --all_defs_and_premises {}  > dataset/{= s@./raw_dataset@@ ; s@.fst@.fst.json@ =}'
	find ./raw_dataset -type f -name "*.fsti" | parallel  -j8 -replace='{}' '../ocaml/bin/fstar_insights.exe --include ./raw_dataset --include ./ --all_defs_and_premises {}  > dataset/{= s@./raw_dataset@@ ; s@.fsti@.fsti.json@ =}'
	find ./dataset -type f -empty -print -delete

build:
	make -C ../ -j


build_raw_dataset_from_gzip: 
	./everest_full_tar_premise_extractor.py

build_raw_dataset_from_src:
	echo "finding in '${EVEREST_HOME}'"
	mkdir -p raw_dataset
	find ${EVEREST_HOME} -type f -name "*.fst" -exec cp {} ./raw_dataset/ \;
	find ${EVEREST_HOME} -type f -name "*.fsti" -exec cp {} ./raw_dataset/ \;
	# find ${EVEREST_HOME} -type f -name "*.hints" -exec cp {} ./raw_dataset/ \;
	find ${EVEREST_HOME} -type f -name "*.checked" -exec cp {} ./raw_dataset/ \;

remove_duplicates:
	@echo "TODO: remove duplicates of paths"

build_corpus_file:
	./build-dataset-for-reprover.py

build_import_graph:
	./build_fstar_import_graph.py

everything:
	build_raw_dataset_from_gzip
	build
	find_all
	remove_duplicates
	build_corpus_file
	build_fstar_import_graph
	zip
