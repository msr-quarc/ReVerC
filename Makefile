VERFILES=Util.fst Maps.fst PairHeap.fst AncillaHeap.fst Circuit.fst BoolExp.fst ExprTypes.fst Interpreter.fst Hack.fst
EX= ext.fst map.fst io.fst listproperties.fst
EXLIB = $(addprefix $(FSTAR_HOME)/lib/, $(EX))
include Makefile.include

ML=FunctionalExtensionality.ml Util.ml PairHeap.ml AncillaHeap.ml Circuit.ml BoolExp.ml ExprTypes.ml Interpreter.ml main.ml
MLFILES = $(addprefix ocaml-src/, $(ML))
SUPPORTFILES=support.ml

#all: .all.ver
all: $(VERFILES)
	$(FSTAR) --z3timeout 60 --admit_fsi Set $(STDLIB) $(EXLIB) $^ --verify_module VerifyHack

cache: .cache

ocamlcode: $(VERFILES)
	$(FSTAR) --codegen OCaml --z3timeout 60 --n_cores 4 --admit_fsi Set $(STDLIB) $(EXLIB) $^
	mv *.ml ocaml-src/

ocaml: $(MLFILES)
	cd ocaml-src &&	$(OCAMLOPT) -o rever $(SUPPORTFILES) $(ML) &&	mv rever ../
