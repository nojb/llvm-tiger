all:
	ocamlbuild test.native

clean:
	ocamlbuild -clean

.PHONY: all clean
