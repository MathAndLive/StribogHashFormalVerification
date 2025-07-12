{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }@attrs:
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = import nixpkgs { inherit system; };
        in
        {
          devShells.default = pkgs.mkShell {
            buildInputs = with pkgs; [ 
              pkg-config
              gmp
                ocaml
            opam
            dune_3
              opam
                                                python3
                alejandra
            ];
          shellHook = ''
            if [ -d "./_opam" ]; then
              eval $(opam env --switch=. --set-switch)
            else
              echo "No local OPAM switch detected. Run 'opam switch create .' if needed."
            fi
          '';
        };
      }
      );
}
