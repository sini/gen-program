# THE IDENTIFIER DOORS' ADMITTING HALF (den-hoag-bkdkg). The refusals are message cells in
# `ci/tests-error.nix`; these are what the doors still answer. The frozen set is consulted only when
# a relatum is looked up in it, so a program with no relata answers whatever the frozen set holds —
# as it did before the guard, and a guard forced ahead of that lookup would refuse it.
{ genProgram, ... }:
{
  flake.tests.identifierDoors = {
    test-declaration-admits-identifiers = {
      expr = genProgram.declaration {
        head = "h";
        pos = [ "p" ];
        relata = [ "x" ];
      };
      expected = {
        head = "h";
        pos = [ "p" ];
        neg = [ ];
        relata = [ "x" ];
      };
    };
    test-unresolvedRelata-with-no-relata-reads-no-frozen-entry = {
      expr = genProgram.unresolvedRelata {
        declarations = [ ];
        frozen = [ { name = "a"; } ];
      };
      expected = [ ];
    };
    # The guards live in the door body, never in a wrapper at the export, and a wrapper is
    # detectable: it erases the formals a caller reads.
    test-declaration-keeps-its-published-formals = {
      expr = builtins.functionArgs genProgram.declaration;
      expected = {
        head = false;
        neg = true;
        pos = true;
        relata = false;
      };
    };
  };
}
