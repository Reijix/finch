
.PHONY: update build optim haddock haddock-serve

all: update build optim

update:
	wasm32-wasi-cabal update

build:
	sass static/sass/style.sass:static/style.css
	wasm32-wasi-cabal build
	mkdir -p public
	cp -r static/* public/
	$(eval my_wasm=$(shell wasm32-wasi-cabal list-bin finch | tail -n 1))
	$(shell wasm32-wasi-ghc --print-libdir)/post-link.mjs --input $(my_wasm) --output public/ghc_wasm_jsffi.js
	cp $(my_wasm) public/

optim:
	wasm-opt -all -O2 public/finch.wasm -o public/finch.wasm
	wasm-tools strip -o public/finch.wasm public/finch.wasm

serve: all
	http-server public

serve-quick: update build optim
	http-server public

clean:
	rm -rf dist-newstyle public docs haddocks

test:
	cabal update
	cabal test

haddock:
	cabal update
	cabal haddock-project --tests --hoogle
	mkdir -p public
	mv -v haddocks public/docs

report:
	cabal update
	cabal test --enable-coverage
