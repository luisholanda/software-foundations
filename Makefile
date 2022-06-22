COQ_MAKEFILE := "MakefileCoq.mk"

COQ_FILES := $(wildcard **/*.v)

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
	@echo "" >> $@
	@echo $(COQ_FILES) >> $@

%: $(COQ_MAKEFILE)
	$(MAKE) -f $(COQ_MAKEFILE) $@

.PHONY: all clean _CoqProject
