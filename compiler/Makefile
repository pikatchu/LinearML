
OCAMLBIN =
OCAMLLIB ?= /usr/lib/ocaml/llvm-2.8

OCAMLC   = ocamlc -dtypes -warn-error A
OCAMLOPT = ocamlopt
OCAMLDEP = ocamldep
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc
CC = g++

LLVM_LIBS = \
	llvm.cma \
	llvm_analysis.cma \
	llvm_bitwriter.cma \
	llvm_scalar_opts.cma \
	llvm_target.cma

#	llvm_bitreader.cma 

LIBS = unix.cma $(LLVM_LIBS)
LIBSOPT = $(LIBS:.cma=.cmxa)
INCLUDE = -I $(OCAMLLIB)
CLIBS = $(addprefix $(OCAMLLIB)/, $(LLVM_LIBS:.cma=.a))

default: limlc

.PHONY: limlc

OBJECTS_ML = \
	genGlobals.ml\
	global.ml\
	pos.ml\
	ident.ml\
	utils.ml\
	error.ml\
	ast.ml\
	lexer.ml\
        parser.ml\
	nast.ml\
	naming.ml\
	nastCheck.ml\
	neast.ml\
	nastExpand.ml\
	neastCheck.ml\
	tast.ml\
	typing.ml\
	stast.ml\
	stastOfTast.ml\
	stastCheck.ml\
	recordCheck.ml\
	linearCheck.ml\
	boundCheck.ml\
	ist.ml\
	istOfStast.ml\
	extractFuns.ml\
	est.ml\
	estSubst.ml\
	estPp.ml\
	estOfIst.ml\
	estOptim.ml\
	estCompile.ml\
	estNormalizePatterns.ml\
	llst.ml\
	llstPp.ml\
	llstOfEst.ml\
	llstFree.ml\
	llstOptim.ml\
	llstRemoveUnit.ml\
	emit.ml\
	main.ml
#	istAdhoc.ml

#	boundCheck2.ml\
# 	id.ml\
# 	ast.ml\
# 	astOfCst.ml\
# 	statesOfAst.ml
#	istRecords.ml\
	istOptim.ml\


OBJECTS_CMO = $(OBJECTS_ML:.ml=.cmo)	
OBJECTS_CMX = $(OBJECTS_ML:.ml=.cmx)	

limlc: $(OBJECTS_CMX) ../stdlib/libliml.a
	echo $(LIBS)
	$(OCAMLOPT) -cc $(CC) $(INCLUDE) -linkall $(CLIBS) $(LIBSOPT) $(OBJECTS_CMX) \
		-o $@		

limlc.bc: $(OBJECTS_CMO) ../stdlib/libliml.a
	$(OCAMLC) -g -cc $(CC) $(INCLUDE) $(LIBS) $(OBJECTS_CMO) \
		-o $@ 

##############################################################################

%.cmo : %.ml
	$(OCAMLC) $(INCLUDE) $(OCAMLC_CFLAGS) -c -g $<

%.cmi : %.mli
	$(OCAMLC) $(OCAMLOPT_CFLAGS) $(INCLUDE) $<  

%.cmx : %.ml
	$(OCAMLOPT) $(OCAMLOPT_CFLAGS) $(INCLUDE) $(PP) -annot -c $<  

%.ml : %.mll
	$(OCAMLLEX) $<

%.ml %.mli : %.mly
	$(OCAMLYACC) -v $<

###############################################################################

genGlobals.ml:
	echo "let root = \"$(STDLIB_PATH)\"" > genGlobals.ml

../stdlib/libliml.a:
	@echo "Compiling the standard library"
	cd ../stdlib && make

.depend: $(OBJECTS_ML)
	$(OCAMLDEP) -native -slash $(INCLUDE) $(OBJECTS_ML) > .depend

clean: 
	rm -f *.cm* pkl *~ lexer.ml parser.ml parser.mli lexer.mli *.o* \#*
	rm -f limlc limlc.bc liml liml.bc *.annot .depend
	rm -f test/*.o test/*.s 
	rm -f test/*.bc test/*~
	rm -f genGlobals.ml
	cd ../stdlib && make clean

-include .depend
-include Makefile.config
