OCAMLBUILD = ocamlbuild -classic-display -use-ocamlfind

all: src/main.native

src/main.native:
	$(OCAMLBUILD) $@

clean:
	$(OCAMLBUILD) -clean

.PHONY: all %.native
