
.PHONY: update build optim haddock haddock-serve

all: update build optim

update:
	wasm32-wasi-cabal update

build:
	wasm32-wasi-cabal build
	rm -rf public
	cp -r static public
	$(eval my_wasm=$(shell wasm32-wasi-cabal list-bin finch | tail -n 1))
	$(shell wasm32-wasi-ghc --print-libdir)/post-link.mjs --input $(my_wasm) --output public/ghc_wasm_jsffi.js
	cp -v $(my_wasm) public/

optim:
	wasm-opt -all -O2 public/finch.wasm -o public/finch.wasm
	wasm-tools strip -o public/finch.wasm public/finch.wasm

serve: all
	http-server public

clean:
	rm -rf dist-newstyle public haddock

test:
	cabal update
	cabal test

haddock:
	wasm32-wasi-cabal haddock --haddock-option="--html --hyperlinked-source" --haddock-quickjump --haddock-output-dir haddock

haddock-serve: haddock
	xdg-open haddock/Finch/index.html

report:
	cabal test --enable-coverage
