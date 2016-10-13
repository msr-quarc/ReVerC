FSTAR_HOME = .fstar

FSTAR = $(FSTAR_HOME)/bin/fstar.exe
FSHARP = fsharpc

FILES = SetExtra.fst Total.fst Partial.fst Util.fst PairHeap.fst AncillaHeap.fst \
				Circuit.fst BoolExp.fst ExprTypes.fst TypeCheck.fst Interpreter.fst \
				Crush.fst Compiler.fst GC.fst
#FILES = Util.fst Maps.fst PairHeap.fst AncillaHeap.fst Circuit.fst BoolExp.fst ExprTypes.fst Interpreter.fst
REVS  = GenOp.fs buddy.fs Equiv.fs Cmd.fs Examples.fs Program.fs
SUPPORT = FStar.Set FStar.Heap FStar.ST FStar.All FStar.List FStar.String FStar.IO

FSFILES = #FStar.FunctionalExtensionality.fs # FStar.Heap.fs FStar.ListProperties.fs FStar.Map.fs FStar.Util.fs

FSTSRC = $(addprefix src/, $(FILES))
FSSRC  = $(addprefix src/fs/, $(STDLIB:.fst=.fs) $(EX:.fst=.fs)  $(FSFILES) $(FILES:.fst=.fs) $(REVS))
LIB 	 = $(addprefix $(FSTAR_HOME)/lib/, $(STDLIB) $(EX))

EXCL   = $(addprefix --no_extract , $(SUPPORT))

DLLS = $(FSTAR_HOME)/lib/fs/fstarlib.dll $(FSTAR_HOME)/bin/FSharp.PowerPack.dll $(FSTAR_HOME)/bin/FSharp.PowerPack.Compatibility.dll
FSOPS = $(addprefix -r , $(DLLS))

verify: $(FSTSRC)
	$(FSTAR) --z3timeout 300 $^

hints: $(FSTSRC)
	$(FSTAR) --z3timeout 300 --record_hints --use_hints $^ --verify_module GC

fs: $(FSTSRC)
	$(FSTAR) --admit_smt_queries true --codegen FSharp $(EXCL) $^
#	mv *.fs src/fs/

revs: $(FSSRC)
	$(FSHARP) --mlcompatibility $(FSOPS) -o reverc.exe $^
