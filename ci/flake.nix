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

    # The one term algebra (den-hoag-lwbb1 unit 1) and the minting authority it is applied to,
    # reached THROUGH gen-scope's pin for the prelude's reason above: two mints in one acceptance
    # run would make an identity cell a question about which copy answered.
    gen-algebra.url = "github:sini/gen-algebra";
    gen-identity.follows = "gen-scope/gen-identity";
  };

  outputs =
    inputs@{
      gen-harness,
      gen-scope,
      gen-algebra,
      gen-identity,
      ...
    }:
    let
      scope = gen-scope.lib;
      prelude = gen-scope.inputs.gen-prelude.lib;
      algebra = gen-algebra.lib;
      identity = gen-identity.lib;
      genProgram = import ../lib {
        inherit
          prelude
          scope
          algebra
          identity
          ;
      };
      # The term instance a test writes a rule body in: the same algebra applied to the same mint
      # the library applies, so a term built here and one built there have one identity.
      T = algebra.term identity.hashIdentity;
    in
    gen-harness.lib.mkCi {
      inherit inputs;
      name = "gen-program";
      testModules = ./tests;
      specialArgs = {
        inherit
          genProgram
          scope
          prelude
          algebra
          identity
          T
          ;
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
