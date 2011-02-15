
CC = gcc
CC_OPT = -O3 -fPIC
CC_ARCH = -DARCH_32

default: libliml.so.1

.PHONY: libliml.so.1

SOURCES =\
	array.c\
	print.c\
	math.c\
	debug.c

OBJECTS = $(SOURCES:.c=.o)	

libliml.so.1: $(OBJECTS)
	@rm -f libliml.so.1 libliml.so
	gcc -shared -Wl,-soname,libliml.so \
		    -o libliml.so.1 $(OBJECTS) $(LIBS)
	ln -s libliml.so.1 libliml.so

##############################################################################

%.o : %.c
	$(CC) $(CC_OPT) $(CC_ARCH) -c $<


###############################################################################

clean: 
	rm -f *.o *~ libliml.so.1 libliml.so \#*

