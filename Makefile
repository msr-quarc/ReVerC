FSTAR_HOME = /home/meamy/Programming/FStar

FSTAR = $(FSTAR_HOME)/bin/fstar.exe
FSHARP = fsharpc

FILES = Util.fst Total.fst Par.fst PairHeap.fst AncillaHeap.fst Circuit.fst BoolExp.fst ExprTypes.fst Interpreter.fst
STDLIB = FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst FStar.String.fsti
EX = FStar.Map.fst FStar.IO.fsti FStar.ListProperties.fst

FSFILES =

FSTSRC = $(addprefix src/, $(FILES))
FSSRC  = $(addprefix src/fs/, $(STDLIB:.fst=.fs) $(EX:.fst=.fs)  $(FSFILES) $(FILES:.fst=.fs))
LIB 	 = $(addprefix $(FSTAR_HOME)/lib/, $(STDLIB) $(EX))

DLLS = $(FSTAR_HOME)/lib/fs/fstarlib.dll $(FSTAR_HOME)/bin/FSharp.PowerPack.dll $(FSTAR_HOME)/bin/FSharp.PowerPack.Compatibility.dll
FSOPS = $(addprefix -r , $(DLLS))

verify: $(FSTSRC)
	$(FSTAR) --z3timeout 60 $^

fs: $(FSTSRC)
	$(FSTAR) --admit_smt_queries true --codegen FSharp $^
	mv *.fs src/fs/

all: $(FSSRC)
	$(FSHARP) --mlcompatibility $(FSOPS) -o rever.exe $(FSSRC)
