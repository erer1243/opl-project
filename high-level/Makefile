.PHONY: repl clean test

hl: hl.hs
	ghc -Wall -Wno-type-defaults -Wno-name-shadowing hl.hs

repl:
	ghci -XOverloadedStrings -XOverloadedLists hl.hs

clean:
	rm -f hl.hi hl.o hl

test: hl
	../low-level/target_ramdisk.sh
	systemd-run --user --scope -p MemoryMax=1500M -p MemorySwapMax=0 ./hl
