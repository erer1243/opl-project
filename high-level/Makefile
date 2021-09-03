.PHONY: repl clean

hl: hl.hs
	ghc hl.hs

repl:
	ghci -XOverloadedStrings -XOverloadedLists hl.hs

clean:
	rm -f hl.hi hl.o hl
