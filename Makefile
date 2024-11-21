all:
	-cd main; $(MAKE) $(MFLAGS)
	-cd trigo_without_pi; $(MAKE) $(MFLAGS)
	-cd rngl_alg; $(MAKE) $(MFLAGS)

clean:
	cd main; $(MAKE) clean
	cd trigo_without_pi; $(MAKE) clean
	cd rngl_alg; $(MAKE) clean
