
.PHONY= update build optim

all: update build optim serve

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

serve:
	http-server public

clean:
	rm -rf dist-newstyle public

test:
	cabal test

report:
	cabal test --enable-coverage
