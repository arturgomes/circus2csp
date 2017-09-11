# Makefile for compiling and testing the Z animator under GHC.
.SUFFIXES: .o .hi ..lhs .hs .hc .s

# Enable profiling (turn off -auto-all for EParseLib, Parse, Formatting )
# NOTE: you must also disable readline in TextUI.lhs.
# GHCFLAGS=-syslib text -syslib util -static -prof -auto-all

#GHCFLAGS=-syslib text -syslib util -static
GHCFLAGS=-static

TESTS=eval_test unfold_test lexer_test parse_test formatter_test subs_test \
      reorder_test
PROGS=jaza clpstests

COREOBJ=AST.o Errors.o
LEXEROBJ=EParseLib.o Lexer.o
PARSEOBJ=$(LEXEROBJ) Parse.o
EVALOBJ=$(PARSEOBJ) FiniteSets.o Subs.o Reorder.o SetSize.o Eval.o
ANIMOBJ=$(COREOBJ) $(EVALOBJ) Formatter.o Animate.o Optimize.o Unfold.o MappingFunStatelessCircus.o

all: $(PROGS) $(TESTS)

help:
	@echo "Possible make targets include:"
	@echo "  circus   -- compile jaza with GHC"
	@echo "  clean  -- remove generated files"
	@echo "  tags   -- make TAGS file for Emacs"



# Note: -lHSutil -lreadline -lncurses flags have to go in this order,
#       otherwise the linker does not search them in the correct order.
JAZAOBJ=$(ANIMOBJ) TextUI.o
CIRCUSOBJ=$(ANIMOBJ) CircusUI.o
jaza: $(JAZAOBJ)
	ghc $(GHCFLAGS) -o jaza --make TextUI.lhs

circus: $(CIRCUSOBJ)
	ghc -w $(GHCFLAGS) -o circus --make CircusUI.lhs




wc:
	wc $(ANIMOBJ:.o=..lhs)

test: $(TEST)
	for t in $(TESTS); do echo $$t; ./$$t; done

# Definitions for creating releases.
DOCS=jaza/README jaza/COPYING \
     jaza/userman/master.pdf jaza/userman/bbook.zed
# TODO: add  jaza/examples/*.zed
TESTSRC=jaza/tests/Makefile jaza/tests/*.jaza

# This makes a source release.
srcrel:
	cd ..; tar czvf jaza_source.tgz $(DOCS) jaza/*.lhs jaza/*.lhs $(TESTSRC)

winrel:
	cd ..; zip jaza_winxp.zip $(DOCS) jaza/jaza.exe $(TESTSRC)

# This makes a binary release.
binrel: jaza
	strip jaza
	cd ..; tar czvf jaza_linux.tgz $(DOCS) jaza/jaza $(TESTSRC)

tags:
	rm -f TAGS
	hstags $(GHC_FLAGS) *.hs *.lhs

clean:
	rm -f *.o *.hi *.aux *.log *.out *.fls *.fdb_latexmk

depend:
	ghc -M $(GHCFLAGS) *.lhs FiniteSets.lhs

eval_test: $(COREOBJ) $(EVALOBJ) Eval_Test.o
	ghc $(GHCFLAGS) -o eval_test $(COREOBJ) $(EVALOBJ) Eval_Test.o

lexer_test: $(COREOBJ) $(LEXEROBJ) Lexer_Test.o
	ghc $(GHCFLAGS) -o lexer_test $(COREOBJ) $(LEXEROBJ) Lexer_Test.o

parse_test: $(COREOBJ) $(PARSEOBJ) Parse_Test.o Test_Strings.o
	ghc $(GHCFLAGS) -o parse_test $(COREOBJ) $(PARSEOBJ) Parse_Test.o Test_Strings.o

formatter_test: $(COREOBJ) $(PARSEOBJ) FiniteSets.o Formatter.o Formatter_Test.o Test_Strings.o
	ghc $(GHCFLAGS) -o formatter_test --make Formatter_Test.lhs
	# WAS $(COREOBJ) $(PARSEOBJ) FiniteSets.o Formatter.o Formatter_Test.o Test_Strings.o

unfold_test: $(COREOBJ) $(EVALOBJ) Unfold.o Unfold_Test.o
	ghc $(GHCFLAGS) -o unfold_test --make Unfold_Test.lhs
	# WAS: $(COREOBJ) $(EVALOBJ) Unfold.o Unfold_Test.o

subs_test: $(COREOBJ) $(PARSEOBJ) Unfold.o FiniteSets.o Formatter.o Subs.o Subs_Test.o
	ghc $(GHCFLAGS) -o subs_test --make Subs_Test.lhs
	# WAS: $(COREOBJ) $(PARSEOBJ) Unfold.o FiniteSets.o Formatter.o Subs.o Subs_Test.o

reorder_test: $(COREOBJ) $(PARSEOBJ) Unfold.o FiniteSets.o Formatter.o Subs.o SetSize.o Reorder.o ReorderTest.o
	ghc $(GHCFLAGS) -o reorder_test --make ReorderTest.lhs
	# WAS: $(COREOBJ) $(PARSEOBJ) Unfold.o FiniteSets.o Formatter.o Subs.o SetSize.o Reorder.o ReorderTest.o


%.hi: %.o
	@:     # do nothing (just record the dependency of .hi on .o)

%.o: %.lhs
	ghc $(GHCFLAGS) -c $<

#%.hi: %..lhs
#	ghc $(GHCFLAGS) -c $<

%.o: %..lhs
	ghc $(GHCFLAGS) -c $<





# DO NOT DELETE: Beginning of Haskell dependencies
AST.o : AST.lhs
Animate.o : Animate.lhs
Animate.o : MappingFunCircusCSP.hi
Animate.o : MappingFunStatelessCircus.hi
Animate.o : ./Errors.hi
Animate.o : ./Eval.hi
Animate.o : ./Optimize.hi
Animate.o : ./Unfold.hi
Animate.o : ./Parse.hi
Animate.o : AST.hi
CRL.o : CRL.lhs
CRL.o : OmegaDefs.hi
CRL.o : AST.hi
EParseLib.o : EParseLib.lhs
EParseTest.o : EParseTest.lhs
EParseTest.o : EParseLib.hi
Errors.o : Errors.lhs
Errors.o : AST.hi
Eval.o : Eval.lhs
Eval.o : ./Reorder.hi
Eval.o : ./Subs.hi
Eval.o : ./FiniteSets.hi
Eval.o : ./SetSize.hi
Eval.o : Errors.hi
Eval.o : AST.hi
Formatter.o : Formatter.lhs
Formatter.o : ./FiniteSets.hi
Formatter.o : ./Parse.hi
Formatter.o : AST.hi
HigherOrder.o : HigherOrder.lhs
Lexer.o : Lexer.lhs
Lexer.o : EParseLib.hi
MappingFunCircusCSP.o : MappingFunCircusCSP.lhs
MappingFunCircusCSP.o : OmegaDefs.hi
MappingFunCircusCSP.o : MappingFunStatelessCircus.hi
MappingFunCircusCSP.o : CRL.hi
MappingFunCircusCSP.o : AST.hi
MappingFunStatelessCircus.o : MappingFunStatelessCircus.lhs
MappingFunStatelessCircus.o : CRL.hi
MappingFunStatelessCircus.o : OmegaDefs.hi
MappingFunStatelessCircus.o : AST.hi
Optimize.o : Optimize.lhs
Optimize.o : Eval.hi
Optimize.o : ./Unfold.hi
Optimize.o : ./Reorder.hi
Optimize.o : ./Subs.hi
Optimize.o : AST.hi
Parse.o : Parse.lhs
Parse.o : Errors.hi
Parse.o : AST.hi
Parse.o : Lexer.hi
Parse.o : EParseLib.hi
Reorder.o : Reorder.lhs
Reorder.o : Parse.hi
Reorder.o : ./Subs.hi
Reorder.o : ./SetSize.hi
Reorder.o : AST.hi
ReorderTest.o : ReorderTest.lhs
ReorderTest.o : Reorder.hi
ReorderTest.o : Formatter.hi
ReorderTest.o : ./Unfold.hi
ReorderTest.o : Parse.hi
ReorderTest.o : Errors.hi
ReorderTest.o : AST.hi
SetSize.o : SetSize.lhs
SetSize.o : ./FiniteSets.hi
SetSize.o : Errors.hi
SetSize.o : AST.hi
Subs.o : Subs.lhs
Subs.o : ./FiniteSets.hi
Subs.o : AST.hi
TextUI.o : TextUI.lhs
TextUI.o : Formatter.hi
TextUI.o : Animate.hi
TextUI.o : Errors.hi
TextUI.o : AST.hi
CircusUI.o : CircusUI.lhs
CircusUI.o : MappingFunStatelessCircus.hi
CircusUI.o : Formatter.hi
CircusUI.o : Animate.hi
CircusUI.o : Errors.hi
CircusUI.o : AST.hi
Unfold.o : Unfold.lhs
Unfold.o : Subs.hi
Unfold.o : ./FiniteSets.hi
Unfold.o : Errors.hi
Unfold.o : AST.hi
FiniteSets.o : FiniteSets.lhs
FiniteSets.o : AST.hi
# DO NOT DELETE: End of Haskell dependencies
