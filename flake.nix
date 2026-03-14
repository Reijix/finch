{

  inputs = {
    miso.url = "github:dmjio/miso";
  };

  outputs = inputs:
    inputs.miso.inputs.flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = inputs.miso.inputs.nixpkgs.legacyPackages.${system};
      in {
        devShell = inputs.miso.outputs.devShells.${system}.wasm.overrideAttrs (old: {
          name = "wasm";
          buildInputs = (old.buildInputs or []) ++ [ pkgs.sass ];
        });
        devShells.test = inputs.miso.outputs.devShells.${system}.default;
      });
}
