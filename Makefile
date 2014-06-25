all:
	ocamlbuild -use-ocamlfind src/tigerc.native

clean:
	ocamlbuild -clean

.PHONY: all clean
