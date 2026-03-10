{

  inputs = {
    miso.url = "github:dmjio/miso";
  };

  outputs = inputs:
    inputs.miso.inputs.flake-utils.lib.eachDefaultSystem (system: {
      devShell = inputs.miso.outputs.devShells.${system}.wasm.overrideAttrs {
        name = "wasm";
      };
      devShells.test = inputs.miso.outputs.devShells.${system}.default;
    });
}
