all:
	cd main; $(MAKE)
	cd trigo_without_pi; $(MAKE)
	cd rngl_alg; $(MAKE)

clean:
	cd main; $(MAKE) clean
	cd trigo_without_pi; $(MAKE) clean
	cd rngl_alg; $(MAKE) clean
