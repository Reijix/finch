
CABAL_OPTIONS = --allow-newer --with-compiler=javascript-unknown-ghcjs-ghc --with-hc-pkg=javascript-unknown-ghcjs-ghc-pkg --with-hsc2hs=javascript-unknown-ghcjs-hsc2hs

.PHONY: update build serve

all: build

update:
	cabal update $(CABAL_OPTIONS)

build:
	cabal build $(CABAL_OPTIONS) finch
	rm -rf public
	cp -r $(shell cabal list-bin finch --verbose=0 $(CABAL_OPTIONS)).jsexe public
	cp static/* public

serve1:
	http-server public

serve: all serve1

clean:
	rm -rf dist-newstyle public

test:
# no CABAL_OPTIONS because ghcjs backend does not work with tests...
	cabal update
	cabal test

report:
	cabal test --enable-coverage
