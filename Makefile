
CABAL_OPTIONS = --allow-newer --with-compiler=javascript-unknown-ghcjs-ghc --with-hc-pkg=javascript-unknown-ghcjs-ghc-pkg

.PHONY: update build serve

all: update build

update:
	cabal update

build:
	cabal build $(CABAL_OPTIONS)
	rm -rf public
	cp -r $(shell cabal list-bin fitch-editor-FOL $(CABAL_OPTIONS)).jsexe public
	cp static/* public

serve1:
	http-server public

serve: all serve1

clean:
	rm -rf dist-newstyle public

test:
	cabal test

report:
	cabal test --enable-coverage
