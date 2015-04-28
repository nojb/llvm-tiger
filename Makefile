OCAMLBUILD = ocamlbuild -classic-display -use-ocamlfind

all: src/tigerc.native

%.native:
	$(OCAMLBUILD) $@

clean:
	$(OCAMLBUILD) -clean

.PHONY: all %.native
