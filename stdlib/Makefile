
CC = gcc


default: libliml.so.1

.PHONY: libliml.so.1

SOURCES =\
	array.c\
	print.c

OBJECTS = $(SOURCES:.c=.o)	

libliml.so.1: $(OBJECTS)
	@rm -f libliml.so.1 libliml.so
	gcc -shared -Wl,-soname,libliml.so \
		    -o libliml.so.1 $(OBJECTS) $(LIBS)
	ln -s libliml.so.1 libliml.so

##############################################################################

%.o : %.c
	$(CC) $(CC_FLAGS) -c $<


###############################################################################

clean: 
	rm -f *.o *~ libliml.so.1 libliml.so \#*

