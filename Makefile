# A tiny generic Makefile for Coq projects.

# The variable COQINCLUDE should be defined externally.
# We automatically add the current directory to it.

.PHONY: all clean ide

COQC   := coqc
COQDEP := coqdep
COQIDE := coqide

V      := $(wildcard *.v)
VO     := $(patsubst %.v,%.vo,$(V))
VD     := $(patsubst %.v,%.v.d,$(V))

all: $(VO)

clean:
	rm -f *.vo *.v.d *.glob

ide:
	$(COQIDE) $(COQINCLUDE) -I .

ifeq ($(findstring $(MAKECMDGOALS),clean),)
-include $(VD)
endif

%.v.d: %.v
	@$(COQDEP) $(COQINCLUDE) -I . $< > $@

%.vo: %.v
	$(COQC) $(COQINCLUDE) -I . $<

