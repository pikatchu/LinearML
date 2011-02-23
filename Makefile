
default: compiler/limlc

.PHONY: compiler/limlc

compiler/limlc: Makefile.config
	cd compiler && make

stdlib/libliml.lmli: compiler/limlc
	@echo "Compiling the standard library"
	cd stdlib && make

clean: 
	rm -f *~
	cd compiler && make clean
	cd stdlib && make clean