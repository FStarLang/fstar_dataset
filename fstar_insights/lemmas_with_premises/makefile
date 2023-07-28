.PHONY: find_all build build_raw_dataset

zip:
	tar -czv -f dataset.tar.gz ./dataset

find_all: build
	mkdir -p dataset/
	find ./raw_dataset -type f -name "*.fst" | parallel  -j8 -replace='{}' '../ocaml/bin/fstar_insights.exe --include ./raw_dataset --include ./ --all_defs_and_premises {}  > dataset/{= s@./raw_dataset@@ ; s@.fst@.fst.json@ =}'
	find ./raw_dataset -type f -name "*.fsti" | parallel  -j8 -replace='{}' '../ocaml/bin/fstar_insights.exe --include ./raw_dataset --include ./ --all_defs_and_premises {}  > dataset/{= s@./raw_dataset@@ ; s@.fsti@.fsti.json@ =}'
	find ./dataset -type f -empty -print -delete

build:
	make -C ../ -j

build_raw_dataset:
	echo "finding in '${EVEREST_HOME}'"
	mkdir -p raw_dataset
	find ${EVEREST_HOME} -type f -name "*.fst" -exec cp {} ./raw_dataset/ \;
	find ${EVEREST_HOME} -type f -name "*.fsti" -exec cp {} ./raw_dataset/ \;
	# find ${EVEREST_HOME} -type f -name "*.hints" -exec cp {} ./raw_dataset/ \;
	find ${EVEREST_HOME} -type f -name "*.checked" -exec cp {} ./raw_dataset/ \;


everything:
	build_raw_dataset
	build
	find_all
	zip
