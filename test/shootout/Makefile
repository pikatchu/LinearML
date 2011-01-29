
LIMLC = ../../limlc
LLC = llc -tailcallopt -O3
LINK = llvm-link
OPT = opt
CC = gcc -O3

#	llvm_executionengine.cma

LIML_LIBS = ../../stdlib/*.lml
CC_LIBS = -lpthread -lm

default: fankuch bintree spectral


FILES_LIML = \
	bintree.lml

BC_FILES = \
	../../stdlib/iarray.bc \
	../../stdlib/farray.bc \
	Print.bc\
	List.bc \
	FloatArray.bc \
	IntBox.bc \
	Future.bc \
	BinaryTree.bc \
	SpectralNorm.bc \
	Fankuch.bc 

STDLIB_OBJS = ../../stdlib/*.o

.PHONY: objects

objects: $(FILES_LIML)
	$(LIMLC) $(LIML_LIBS) *.lml

bintree: objects $(BC_FILES) custom_lib.o bintree_main.o
	$(LINK) $(BC_FILES) -o bintree.bc
	$(OPT) -std-link-opts bintree.bc -o bintree_opt.bc
	$(LLC) bintree_opt.bc
	$(CC) bintree_opt.s $(STDLIB_OBJS) custom_lib.o bintree_main.o $(CC_LIBS) -o $@ 

spectral: objects $(BC_FILES) custom_lib.o spectral_main.o
	$(LINK) ../../stdlib/farray.bc Print.bc	FloatArray.bc SpectralNorm.bc -o spectral.bc
	$(OPT) -std-link-opts spectral.bc -o spectral_opt.bc
	$(LLC) spectral_opt.bc
	$(CC) spectral_opt.s $(STDLIB_OBJS) custom_lib.o spectral_main.o $(CC_LIBS) -o $@ 

fankuch: objects $(BC_FILES) custom_lib.o fankuch_main.o
	$(LINK) ../../stdlib/iarray.bc IntArray.bc Fankuch.bc Print.bc -o fankuch.bc
	$(OPT) -std-link-opts fankuch.bc -o fankuch_opt.bc
	$(LLC) fankuch_opt.bc
	$(CC) fankuch_opt.s $(STDLIB_OBJS) custom_lib.o fankuch_main.o $(CC_LIBS) -pg -o $@ 


%.o : %.c
	$(CC) -c $<

clean: 
	rm -f ./bintree ./spectral ./fankuch
	rm -f *.o *.s *.bc *~ test/*.o test/*.s 

