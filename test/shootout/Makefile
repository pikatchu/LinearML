
LIMLC = ../../limlc
LLC = llc -tailcallopt
CC = gcc -O3

#	llvm_executionengine.cma

LIML_LIBS = ../../stdlib/*.lml
CC_LIBS = -lpthread -lm

default: bintree spectral 


FILES_LIML = \
	bintree.lml

MODULES_LIML = \
	Print.bc\
	List.bc \
	IntBox.bc \
	Future.bc \
	BinaryTree.bc \
	SpectralNorm.bc 

STDLIB_OBJS = ../../stdlib/*.o
FILES_ASM = $(MODULES_LIML:.bc=.s)

.PHONY: objects

objects: $(FILES_LIML)
	$(LIMLC) $(LIML_LIBS) *.lml

bintree: objects $(FILES_ASM) custom_lib.o bintree_main.o
	$(CC) $(FILES_ASM) $(STDLIB_OBJS) custom_lib.o bintree_main.o $(CC_LIBS) -o $@ 

spectral: objects $(FILES_ASM) custom_lib.o spectral_main.o
	$(CC) $(FILES_ASM) $(STDLIB_OBJS) custom_lib.o spectral_main.o $(CC_LIBS) -o $@ 


%.s : %.bc
	$(LLC) $<

%.o : %.c
	$(CC) -c $<

clean: 
	rm -f ./bintree ./spectral
	rm -f *.o *.s *.bc *~ test/*.o test/*.s 

