
LIMLC = ../../compiler/limlc


default: fankuch.run bintree_2.run

%.run: %.lml
	$(LIMLC) $< -root Main -o $@

clean: 
	rm -f ./bintree.run ./spectral.run ./fankuch.run
	rm -f *.o *.s *.bc *~ test/*.o test/*.s 

