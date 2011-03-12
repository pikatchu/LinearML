-include ../Makefile.config

CC_OPT = -O3

default: libliml.a

.PHONY: libliml.a

SOURCES =\
	array.c\
	print.c\
	math.c\
	string.c\
	debug.c

LML_SOURCES =\
	pervasives.lml\
	array.lml \
	print.lml \
	string.lml \
	list.lml

OBJECTS = $(SOURCES:.c=.o)	

libliml.a: $(OBJECTS) $(LML_SOURCES)
	@rm -f libliml.a
	../compiler/limlc -no-stdlib $(LML_SOURCES) -lib libliml.lmli 
	$(AR) r libliml.a $(OBJECTS)

##############################################################################

%.o : %.c
	$(CC) $(CC_OPT) $(CC_ARCH) -c $<


###############################################################################

clean: 
	rm -f *.o *~ libliml.a \#*

