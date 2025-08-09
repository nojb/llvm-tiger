.PHONY: all
all:
	dune build

.PHONY: test
test:
	dune runtest --auto-promote