{
  inputs = {
    gen-harness.url = "github:sini/gen-harness";

    # nixpkgs is the CI runner's dependency (nix-unit harness, treefmt) and supplies the `lib` the
    # test modules use — including, here, to run the purity scan itself. It enters ONLY in ci/,
    # never as a `lib/` dep: the library (../lib) is nixpkgs-lib-free, which ci/tests/purity.nix
    # enforces.
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";

    # THE SUBSTRATE. The library takes it injected, so the library itself declares no dependency
    # on it — but the ACCEPTANCE RUN must supply one, and gen-scope is it. The prelude is reached
    # THROUGH that pin rather than declared beside it: this library compares values that cross the
    # boundary between the two, and two prelude instances would make an equality cell a question
    # about which copy answered.
    gen-scope.url = "github:sini/gen-scope";
  };

  outputs =
    inputs@{ gen-harness, gen-scope, ... }:
    let
      scope = gen-scope.lib;
      prelude = gen-scope.inputs.gen-prelude.lib;
      genProgram = import ../lib { inherit prelude scope; };
    in
    gen-harness.lib.mkCi {
      inherit inputs;
      name = "gen-program";
      testModules = ./tests;
      specialArgs = {
        inherit genProgram scope prelude;
      };
      # Cells whose subject is an error MESSAGE cannot live under `testModules`: the batch
      # asserter behind `checks.default` quantifies over `flake.tests` and forces every `expr`
      # unconditionally, so a cell with no `expected` and a throwing `expr` CRASHES that gate
      # instead of failing it. They get their own output, read by
      # `nix-unit --flake ./ci#testsError`, and being outside ./tests is what keeps that split
      # structural rather than conventional.
      extraModules = [
        ./tests-error.nix
      ];
    };
}
