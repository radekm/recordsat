
.PHONY: all clean

all:
	ocamlbuild -use-ocamlfind recordSat.native

clean:
	ocamlbuild -clean

