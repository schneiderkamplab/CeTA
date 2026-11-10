EX_FILES:=$(shell ls examples/*.proof.xml)
EX_FILES2:=$(shell ls examples/*.cpf.xml)
HASKELL=Haskell
GHC?=ghc
CETA_BUILD_DIR?=target/haskell
CETA_BIN_DIR?=.
STATIC=
override GHC_ARGS:= -package array -XRankNTypes $(filter-out -O -O0 -O1 -O2 -O3,$(GHC_ARGS)) -O2 $(if $(STATIC), -static -optl-static -optl-pthread, )
SRC=src
GENERATED=generated
ISABELLE?=isabelle
ISABELLE_JOBS?=16
ISABELLE_DIRS=$(if $(AFP),-d "$(AFP)") -d thys
OK=echo -e "\0033[1000D\0033[1A\0033[59C[\0033[32m  OK  \0033[0m]"
OK_ASS=echo -e "\0033[1000D\0033[1A\0033[59C[\0033[32mOK ASS\0033[0m]"
ERROR=echo -e "\0033[1000D\0033[1A\0033[59C[\0033[31mFAILED\0033[0m]"
MAKE=make --no-print-directory

all: ceta
	@echo 'You can now check your proofs calling '
	@echo
	@echo 'ceta <cpfFile>'
	@echo
	@echo 'to test ceta just call "make test"'


test: ceta
	@echo "Testing examples"
	@echo
	@for i in $(EX_FILES); do \
	   echo $$i; \
	   "$(CETA_BIN_DIR)/ceta" $$i > /dev/null 2> /dev/null ;  if [ $$? != 0 ]; then $(ERROR); else $(OK); fi; \
	done 
	@echo
	@echo "Testing examples (separate input, property, answer, and proof)"
	@echo
	@for cpf in $(EX_FILES2); do \
	   input=$${cpf%.cpf.xml}.input.xml; \
	   property=$${cpf%.cpf.xml}.property; \
	   answer=$${cpf%.cpf.xml}.answer; \
	   echo "$${cpf%.cpf.xml}.input.xml|.property|.answer|.cpf.xml" ; \
	   "$(CETA_BIN_DIR)/ceta" --inputf $$input --propertyf $$property --answerf $$answer $$cpf > /dev/null 2> /dev/null ;  if [ $$? != 0 ]; then $(ERROR); else $(OK); fi; \
	done 
	@echo "   "

CETA_UNIFIED_BUILD_DIR?=target/unified
CETA_BUILD_JOBS?=4

.PHONY: ceta ceta-unified
ceta: ceta-unified

ceta-unified:
	GHC="$(GHC)" python3 scripts/build_unified_checker.py --output "$(CETA_UNIFIED_BUILD_DIR)" --jobs "$(CETA_BUILD_JOBS)"
	@mkdir -p "$(CETA_BIN_DIR)"
	cp "$(CETA_UNIFIED_BUILD_DIR)/ceta" "$(CETA_BIN_DIR)/ceta"

ceta-ordinary:
	@mkdir -p "$(CETA_BUILD_DIR)/ordinary" "$(CETA_BIN_DIR)"
	$(GHC) $(GHC_ARGS) -i$(GENERATED)/$(HASKELL) -odir "$(CETA_BUILD_DIR)/ordinary" -hidir "$(CETA_BUILD_DIR)/ordinary" --make $(SRC)/$(HASKELL)/Main.hs -o "$(CETA_BIN_DIR)/ceta-ordinary"

ceta-relative-adp:
	@mkdir -p "$(CETA_BUILD_DIR)/relative-adp" "$(CETA_BIN_DIR)"
	$(GHC) $(GHC_ARGS) -i$(GENERATED)/$(HASKELL) -odir "$(CETA_BUILD_DIR)/relative-adp" -hidir "$(CETA_BUILD_DIR)/relative-adp" --make $(SRC)/$(HASKELL)/Main_Relative_ADP.hs -o "$(CETA_BIN_DIR)/ceta-relative-adp"

test-relative-adp: ceta-relative-adp
	"$(CETA_BIN_DIR)/ceta-relative-adp" examples/relative_adp_rt1_3.cpf.xml

haskell:
	@mkdir -p "$(CETA_BUILD_DIR)/rfc" "$(CETA_BIN_DIR)"
	$(GHC) $(GHC_ARGS) -i$(GENERATED)/$(HASKELL) -odir "$(CETA_BUILD_DIR)/rfc" -hidir "$(CETA_BUILD_DIR)/rfc" --make $(SRC)/$(HASKELL)/Main_RFC.hs -o "$(CETA_BIN_DIR)/ceta"

clean:
	@echo "Cleaning directory"
	@rm -f $(GENERATED)/$(HASKELL)/*.hi $(GENERATED)/$(HASKELL)/*.o
	@for flavor in rfc ordinary relative-adp; do \
	  rm -f "$(CETA_BUILD_DIR)/$$flavor/"*.hi "$(CETA_BUILD_DIR)/$$flavor/"*.o; \
	done
	@rm -f "$(CETA_BIN_DIR)/ceta" "$(CETA_BIN_DIR)/ceta-ordinary" "$(CETA_BIN_DIR)/ceta-relative-adp"
	@$(OK)

isabelle-proof-base:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) Proof_Checker_Base

isabelle-trs-standard-spec: isabelle-category-specifications

isabelle-category-specifications:
	$(ISABELLE) build -D thys/Category_Specifications

isabelle-trs-standard-bridge: isabelle-category-specification-bridges

isabelle-category-specification-bridges:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) -D thys/Category_Bridges/Bridge

isabelle-csr-base:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) CSR_Checker_Base

isabelle-csr-core:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) CSR_Checker_Core

isabelle-csr-extensions:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) CSR_Checker_Extensions

isabelle-proof-checker:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) Proof_Checker

isabelle-rfc-absolute:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) -d thys/RFC_Absolute_Ext RFC_Absolute_Ext

.PHONY: all clean haskell ceta ceta-ordinary ceta-relative-adp test-relative-adp test isabelle-proof-base isabelle-csr-base \
	isabelle-csr-core isabelle-csr-extensions isabelle-proof-checker isabelle-rfc-absolute \
	isabelle-trs-standard-spec isabelle-trs-standard-bridge

.PHONY: isabelle-category-specifications isabelle-category-specification-bridges

.PHONY: isabelle-trs-standard-integrated
isabelle-trs-standard-integrated:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) -D thys/Category_Bridges/Integrated

.PHONY: isabelle-trs-innermost-integrated
isabelle-trs-innermost-integrated:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) -D thys/Category_Bridges/Innermost_Integrated

.PHONY: isabelle-trs-relative-integrated
isabelle-trs-relative-integrated:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) -D thys/Category_Bridges/Relative_Integrated

.PHONY: isabelle-trs-context-sensitive-integrated
isabelle-trs-context-sensitive-integrated:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) -D thys/Category_Bridges/Context_Sensitive_Integrated

.PHONY: isabelle-srs-standard-integrated
isabelle-srs-standard-integrated:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) -D thys/Category_Bridges/SRS_Integrated

.PHONY: isabelle-srs-relative-integrated
isabelle-srs-relative-integrated: isabelle-srs-standard-integrated

.PHONY: isabelle-higher-order-integrated
isabelle-higher-order-integrated:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) -d thys/Category_Bridges/Higher_Order_Integrated Category_Specifications Category_Higher_Order_Bridge Category_Higher_Order_Integrated

.PHONY: isabelle-outermost-integrated
isabelle-outermost-integrated:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) -d thys/Category_Bridges/Outermost_Integrated Category_Specifications Category_Outermost_Bridge Category_Outermost_Integrated

.PHONY: isabelle-conditional-integrated
isabelle-conditional-integrated:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) -d thys/Category_Bridges/Conditional_Integrated Category_Specifications Category_Conditional_Bridge Category_Conditional_Integrated

.PHONY: isabelle-equational-integrated
isabelle-equational-integrated:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) -d thys/Category_Bridges/Equational_Integrated Category_Specifications Category_Equational_Bridge Category_Equational_Integrated

.PHONY: isabelle-category-properties
isabelle-category-properties:
	$(ISABELLE) build -D thys/Category_Properties

.PHONY: isabelle-its-category-bridge isabelle-lp-category-bridge
isabelle-its-category-bridge:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) -d thys/Category_Bridges/ITS_Bridge Category_ITS_Bridge

isabelle-lp-category-bridge:
	$(ISABELLE) build -j $(ISABELLE_JOBS) $(ISABELLE_DIRS) -d thys/Category_Bridges/LP_Bridge Category_LP_Cut_Triple_Segment_Bridge Category_LP_Advanced_NO_Bridge
