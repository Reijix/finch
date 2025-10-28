
.PHONY= update build optim

all: update build optim

update:
	wasm32-wasi-cabal update

build:
	wasm32-wasi-cabal build 
	rm -rf public
	cp -r static public
	$(eval my_wasm=$(shell wasm32-wasi-cabal list-bin fitch-editor-FOL | tail -n 1))
	$(shell wasm32-wasi-ghc --print-libdir)/post-link.mjs --input $(my_wasm) --output public/ghc_wasm_jsffi.js
	cp -v $(my_wasm) public/

optim:
	wasm-opt -all -O2 public/fitch-editor-FOL.wasm -o public/fitch-editor-FOL.wasm
	wasm-tools strip -o public/fitch-editor-FOL.wasm public/fitch-editor-FOL.wasm

serve:
	http-server public

clean:
	rm -rf dist-newstyle public

test:
	cabal test

report:
	cabal test --enable-coverage
