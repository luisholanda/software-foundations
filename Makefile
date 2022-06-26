COQ_MAKEFILE := "MakefileCoq.mk"

INCLUDE_LF := 1
INCLUDE_VFA := 1

COQ_FILES :=

ifeq ($(INCLUDE_LF),1)
	COQ_FILES += $(wildcard Volume1/*.v)
endif

ifeq ($(INCLUDE_VFA),1)
	COQ_FILES += $(wildcard Volume3/*.v)
endif

COQ_MAKE := $(MAKE) -f $(COQ_MAKEFILE)

all: $(COQ_MAKFILE)
	$(COQ_MAKE) all

fmt: $(COQ_MAKEFILE)
	$(COQ_MAKE) beautify

clean: $(COQ_MAKEFILE)
	@$(COQ_MAKE) cleanall
	@rm -f $(COQ_MAKEFILE) $(COQ_MAKEFILE).conf
	@rm -f *.mli *.ml

$(COQ_MAKEFILE): _CoqProject
	coq_makefile -f _CoqProject -o $(COQ_MAKEFILE)

_CoqProject:
	@echo "-Q Volume1 LF" > $@
	@echo "-Q Volume3 VFA" >> $@
	@echo "" >> $@
	@echo $(COQ_FILES) >> $@

%: $(COQ_MAKEFILE)
	$(COQ_MAKE) $@

.PHONY: all clean _CoqProject
