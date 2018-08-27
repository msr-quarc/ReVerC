FSTAR_HOME = .fstar

FSTAR = $(FSTAR_HOME)/bin/fstar.exe
FSHARP = fsharpc

FILES = SetExtra.fst Total.fst Partial.fst Utils.fst PairHeap.fst AncillaHeap.fst \
				Circuit.fst BoolExp.fst ExprTypes.fst TypeCheck.fst Interpreter.fst \
				Crush.fst Compiler.fst GC.fst
REVLIB  = GenOp.fs buddy.fs Equiv.fs ReVerC.fs
REVS    = Cmd.fs Examples.fs Program.fs
SUPPORT = FStar.Set FStar.Heap FStar.ST FStar.All FStar.List FStar.String FStar.IO

FSTSRC = $(addprefix src/, $(FILES))
FSSRC  = $(addprefix src/fs/, $(FILES:.fst=.fs) $(REVLIB))
REVSRC = $(addprefix reverc/, $(REVS))

EXCL   = $(addprefix --no_extract , $(SUPPORT))

FSOPS = --nowarn:58,62 -r fstarlib.dll

LIBRARY    = reverlib.dll
EXECUTABLE = reverc.exe
ADDERGEN   = adderGen.exe

all: $(EXECUTABLE)

example: $(ADDERGEN)

verify: $(FSTSRC)
	$(FSTAR) --z3rlimit 300 --use_hints $^ 

hints: $(FSTSRC)
	$(FSTAR) --z3rlimit 300 --record_hints --use_hints $^

fs: $(FSTSRC)
	$(FSTAR) --admit_smt_queries true --codegen FSharp $(EXCL) $^
#	mv *.fs src/fs/

$(LIBRARY): $(FSSRC)
	$(FSHARP) --nowarn:25 $(FSOPS) --target:library -o $(LIBRARY) $^

$(EXECUTABLE): $(REVSRC) $(LIBRARY)
	$(FSHARP) $(FSOPS) -r $(LIBRARY) -o $(EXECUTABLE) $(REVSRC)

$(ADDERGEN): examples/AdderGen.fs $(LIBRARY)
	$(FSHARP) $(FSOPS) -r $(LIBRARY) -o $(ADDERGEN) examples/AdderGen.fs
