# <img src="static/icons/favicon.svg" width=32px height=32px> Finch

Finch is a browser-based editor for writing and checking [Fitch-style natural deduction](https://plato.stanford.edu/entries/natural-deduction/#ModeVersJaskMeth) proofs. It supports both **propositional logic** and **first-order logic** (various modal logics might be supported later on), and verifies every line of the proof as you type. The application is compiled from Haskell to WebAssembly using GHC's WASM backend and the [Miso](https://haskell-miso.org) framework, so the entire proof checker runs locally in the browser with no server required.

---

## Features
- Dynamically build proofs using the [HTML5 Drag and Drop API](https://developer.mozilla.org/en-US/docs/Web/API/HTML_Drag_and_Drop_API).
- The checker highlights errors in your proof that you can fix afterwards.
- Highlight text and press '(' to enclose it in parentheses.
- Type aliases like 'forall' to get unicode characters (available aliases are shown in the sidebar).
- View the definitions of all rules of the current logic system in the sidebar, printed using [MathJax](https://www.mathjax.org/).
- Look at exemplary proofs by clicking the corresponding buttons in the sidebar.
- Switch logics in the sidebar.
- Share proofs by sharing the current URL, since proofs are encoded as a `?proof=` [query parameter](https://en.wikipedia.org/wiki/Query_string).

---


## Demo

Visit the automatically hosted website at [finch.vatthauer.xyz](https://finch.vatthauer.xyz).

---


## Documentation

Automatically generated haddock documentation is available at [finch.vatthauer.xyz/docs](https://finch.vatthauer.xyz/docs).

---

## Setup

### Prerequisites

The recommended way to set up the development environment is with [Nix](https://nixos.org). The `flake.nix` at the root of the repository provides a reproducible shell that includes the full WASM toolchain.

With Nix and [flakes](https://nixos.wiki/wiki/Flakes) enabled, enter the development shell with:

```sh
nix develop .
```

### Building

Once inside the Nix shell, build the project with:

```sh
make
```

The finished site lands in the `public/` directory.

### Running locally

```sh
make serve
```

This builds the project and then serves `public/` using [http-server](https://github.com/http-party/http-server).

### Running tests

The test suite requires a regular GHC installation without WASM, this is also provided with Nix:

```sh
nix develop .#test
```

Afterwards you can run the test suite with:

```sh
make test
```

