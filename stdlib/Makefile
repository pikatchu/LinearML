
CC = gcc
CC_OPT = -O3
CC_ARCH = -DARCH_32

default: libliml.a

.PHONY: libliml.a

SOURCES =\
	array.c\
	print.c\
	math.c\
	debug.c

OBJECTS = $(SOURCES:.c=.o)	

libliml.a: $(OBJECTS)
	@rm -f libliml.a
	ar cr libliml.a $(OBJECTS) $(LIBS)

##############################################################################

%.o : %.c
	$(CC) $(CC_OPT) $(CC_ARCH) -c $<


###############################################################################

clean: 
	rm -f *.o *~ libliml.a \#*

