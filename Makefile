all:
	cd main; $(MAKE)

clean:
	cd main; $(MAKE) clean
	cd rngl_alg; $(MAKE) clean
