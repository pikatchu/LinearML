
LIMLC = ../../compiler/limlc


default: fankuch.run bintree.run spectral.run

%.run: %.lml
	$(LIMLC) $< -root Main -o $@

clean: 
	rm -f ./bintree.run ./spectral.run ./fankuch.run
	rm -f *.o *.s *.bc *~ test/*.o test/*.s 

