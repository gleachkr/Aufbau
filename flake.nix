{
  inputs = {
    nixpkgs.url = "nixpkgs";
    utils.url = "github:numtide/flake-utils";
    mm0.url = "github:gleachkr/mm0";
  };

  outputs = { self, nixpkgs, mm0, utils }:
    utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        mm0-rs = mm0.packages.${system}.mm0-rs;
        mm0-c = mm0.packages.${system}.mm0-c;
        zig = pkgs.zig_0_17;
        version = builtins.replaceStrings
          [ "\n" ] [ "" ] (builtins.readFile ./VERSION);
        deps = zig.fetchDeps {
          pname = "mm0-zig";
          inherit version;
          src = self;
          hash = "sha256-RR2ptAUeAdv1DpSy0vyhDLptSu+6cXm+KUHX5du6ZcY=";
        };
        package = pkgs.stdenvNoCC.mkDerivation {
          pname = "mm0-zig";
          inherit version;
          src = self;

          nativeBuildInputs = [ zig ];

          dontSetZigDefaultFlags = true;
          zigBuildFlags = [
            "-Dcpu=baseline"
            "-Doptimize=ReleaseFast"
          ];

          postConfigure = ''
            ln -s ${deps} $ZIG_GLOBAL_CACHE_DIR/p
          '';
        };
      in
      rec {
        packages.default = package;
        defaultPackage = packages.default;

        devShells = {
          default = pkgs.mkShell {
            buildInputs = with pkgs; [
              zig
              zls
              mm0-rs
              mm0-c
              nodejs_22
              mdbook
              hyperfine
              perf
            ];
          };

          ci = pkgs.mkShell {
            packages = [
              zig
              mm0-rs
              mm0-c
              pkgs.nodejs_22
              pkgs.mdbook
            ];
          };
        };
        devShell = devShells.default;
      }
    );
}
