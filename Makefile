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

all: $(COQ_MAKFILE)
	$(MAKE) -f $(COQ_MAKEFILE) all

clean: $(COQ_MAKEFILE)
	@$(MAKE) -f $(COQ_MAKEFILE) cleanall
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
	$(MAKE) -f $(COQ_MAKEFILE) $@

.PHONY: all clean _CoqProject
