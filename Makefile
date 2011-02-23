
default: compiler/limlc

.PHONY: compiler/limlc

compiler/limlc: Makefile.config
	cd compiler && make
