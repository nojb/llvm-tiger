all:
	ocamlbuild tigerc.native

clean:
	ocamlbuild -clean

.PHONY: all clean
