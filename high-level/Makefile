.PHONY: repl clean test

hl: hl.hs
	ghc hl.hs

repl:
	ghci -XOverloadedStrings -XOverloadedLists hl.hs

clean:
	rm -f hl.hi hl.o hl

test: hl
	../low-level/target_ramdisk.sh
	./hl
