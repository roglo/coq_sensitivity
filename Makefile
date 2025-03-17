all:
	cd ring_like; $(MAKE) $(MFLAGS)
	cd trigo_without_pi; $(MAKE) $(MFLAGS)
	cd main; $(MAKE) $(MFLAGS)
	cd rngl_alg; $(MAKE) $(MFLAGS)

clean:
	cd ring_like; $(MAKE) clean
	cd trigo_without_pi; $(MAKE) clean
	cd main; $(MAKE) clean
	cd rngl_alg; $(MAKE) clean
