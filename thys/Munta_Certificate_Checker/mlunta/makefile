build_checker_poly: create_dirs
	polyc -o build/mluntac-poly build.sml

build_checker: create_dirs
	$(mlton) -output build/mluntac-mlton src/checker.mlb

run_perf: build_perf
	cd build && ./perfing && mlprof perfing mlmon.out && cd ..

build_perf: submodule bench.mlb
	$(mlton) -output build/perfing -profile time bench.mlb

run_bench: build_bench_mlton
	./build/bench

build_and_run_bench: submodule build_bench_mlton
	./build/bench

run_test: build_test
	@if [ 0 = $(shell ./build/tests | grep -c "Failed") ]; then\
		echo 'Tests succeeded';\
	else\
		echo 'Tests failed:';\
		./build/tests | grep "Failed";\
		exit 1;\
	fi

build_bench_poly: submodule create_dirs
	polyc -o build/bench build_bench.sml

build_bench_mlton: submodule create_dirs
	$(mlton) -output build/bench bench.mlb

build_test: submodule create_dirs
	polyc -o build/tests build_test.sml

submodule:
	git submodule init
	git submodule update

create_dirs:
	mkdir -p build

clean_test:
	rm -f build/tests

clean:
	rm -f build/*
