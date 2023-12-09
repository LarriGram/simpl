build:
	dune build

utop:
	dune utop src

.PHONY: test
test:
	dune exec test/main.exe
test-coverage:
	dune exec --instrument-with bisect_ppx ./test/main.exe
	bisect-ppx-report html

clean:
	dune clean
	rm bisect*.coverage
