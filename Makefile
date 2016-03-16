FSTAR_HOME = /home/meamy/Programming/FStar

FSTAR = $(FSTAR_HOME)/bin/fstar.exe

FILES = Util.fst Maps.fst PairHeap.fst AncillaHeap.fst Circuit.fst BoolExp.fst ExprTypes.fst Interpreter.fst
STDLIB = FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst FStar.String.fsti
EX = FStar.Map.fst FStar.IO.fsti FStar.ListProperties.fst

SRC = $(addprefix src/, $(FILES))
LIB = $(addprefix $(FSTAR_HOME)/lib/, $(STDLIB) $(EX))

verify: $(SRC)
	$(FSTAR) --z3timeout 60 --explicit_deps $(LIB) $^

fs: $(SRC)
	$(FSTAR) --admit_smt_queries true --codegen FSharp --use_native_int --explicit_deps $(LIB) $^
	mv *.fs src/
