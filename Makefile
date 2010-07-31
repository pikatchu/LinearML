
OCAMLBIN =
OCAMLLIB = /home/pika/godi/lib

OCAMLC   = ocamlc
OCAMLOPT = ocamlopt.opt
OCAMLDEP = ocamldep
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc
CC = g++


LLVM_LIBS = \
	llvm.cma \
	llvm_analysis.cma 
#	llvm_bitwriter.cma \
	llvm_bitreader.cma \
	llvm_executionengine.cma \
	llvm_scalar_opts.cma \
	llvm_target.cma

LIBS = unix.cma $(LLVM_LIBS)
LIBSOPT = $(LIBS:.cma=.cmxa)
INCLUDE = -I $(OCAMLLIB)
CLIBS = $(addprefix $(OCAMLLIB)/, $(LLVM_LIBS:.cma=.a))

default: limlc

.PHONY: limlc

OBJECTS_ML = \
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
	nastExtractFuns.ml\
	nastExpand.ml\
	tast.ml\
	tastRename.ml\
	typing.ml\
	llast.ml\
	emit.ml\
	main.ml
# 	id.ml\
# 	ast.ml\
# 	astOfCst.ml\
# 	statesOfAst.ml

OBJECTS_CMO = $(OBJECTS_ML:.ml=.cmo)	
OBJECTS_CMX = $(OBJECTS_ML:.ml=.cmx)	

limlc: $(OBJECTS_CMX)
	echo $(LIBS)
	$(OCAMLOPT) -cc $(CC) $(INCLUDE) -linkall $(CLIBS) $(LIBSOPT) $(OBJECTS_CMX) -o $@

limlc.bc: $(OBJECTS_CMO)
	$(OCAMLC) -g -cc $(CC) $(INCLUDE) $(LIBS) $(OBJECTS_CMO) -o $@

##############################################################################

%.cmo : %.ml
	$(OCAMLC) $(INCLUDE) $(OCAMLC_CFLAGS) -c -g $<

%.cmi : %.mli
	$(OCAMLC) $(OCAMLOPT_CFLAGS) $(INCLUDE) $<  

%.cmx : %.ml
	$(OCAMLOPT) $(OCAMLOPT_CFLAGS) $(INCLUDE) $(PP) -c $<  

%.ml : %.mll
	$(OCAMLLEX) $<

%.ml %.mli : %.mly
	$(OCAMLYACC) -v $<

###############################################################################

depend: $(OBJECTS_ML)
	$(OCAMLDEP) -native -slash $(INCLUDE) $(OBJECTS_ML) > .depend

clean: 
	rm -f *.cm* pkl *~ lexer.ml parser.ml parser.mli lexer.mli *.o* \#*
	rm -f limlc limlc.bc

include .depend