all:
	cd main; $(MAKE)
	cd rngl_alg; $(MAKE)

clean:
	cd main; $(MAKE) clean
	cd rngl_alg; $(MAKE) clean
