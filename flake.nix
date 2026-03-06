{
  description = "ViE development shell with profiling tools";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in
    {
      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
          linuxProfilingTools =
            pkgs.lib.optionals pkgs.stdenv.isLinux [
              pkgs.linuxPackages.perf
              pkgs.hotspot
            ];
        in
        {
          default = pkgs.mkShell {
            packages =
              [
                pkgs.lean4
                pkgs.elan
                pkgs.git
                pkgs.pijul
                pkgs.gnumake
                pkgs.ripgrep
                pkgs.flamegraph
              ]
              ++ linuxProfilingTools;

            shellHook = ''
              export FLAMEGRAPH_BIN="$(command -v flamegraph.pl || command -v flamegraph || true)"
              export STACKCOLLAPSE_BIN="$(command -v stackcollapse-perf.pl || true)"
              echo "ViE dev shell ready."
              echo "Try: lake build, lake test, ./scripts/perf_bench_bin.sh"
            '';
          };
        });
    };
}
