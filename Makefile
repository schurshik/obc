# obc
# Makefile
# Developer: Branitskiy Alexander <schurshik@yahoo.com>

all: obc.native

obc.native: obc.ml obctypes.ml obcparser.mly
	ocamlbuild -use-menhir -tag thread -use-ocamlfind -quiet -pkg core -pkg str -pkg zarith -pkg core_extended $@

.PHONY: clean install uninstall

clean:
	rm -rf _build obc.native

install:
	cp -f _build/obc.native /usr/bin/obc

uninstall:
	rm -f /usr/bin/obc
