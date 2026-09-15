# THE STANDALONE ENTRY'S OWN DEFAULTS, FORCED — the cell no other cell in this repository can be.
#
# Every other cell here takes `genProgram` from `ci/flake.nix`, which builds it with `import ../lib`
# from ci's own flake INPUTS, so the root shim is never evaluated and its `ci/flake.lock`-backed
# defaults are never forced. That is precisely where this library's non-flake contract lives:
# `import ./. { }` must produce the same library the flake path does, resolving every dependency
# from `./ci/flake.lock` with no argument supplied and no search path consulted.
#
# ★★ THE CALL IS ARITY-DISPATCHED, NOT `import ../.. { }`. A dependency-free library publishes its
# root as a bare VALUE rather than a function, so the literal application is wrong at those roots by
# design; `if builtins.isFunction v then v { } else v` is the one form total over the roster, and it
# is the same construct the shim's own `dep` uses. Writing the literal here would make this cell
# assert a call convention the ecosystem deliberately does not have.
#
# ★★★ THIS CELL IS NOT HERMETIC, AND THAT IS ITS WHOLE POINT. Forcing the defaults IS
# `builtins.fetchTree`, so this cell reaches the network — the accepted price of measuring the thing
# at all, and the reason it sits apart from the suites that must not. It remains PURE: `fetchTree`
# on a locked node is narHash-addressed, with no channel and no `<…>`.
#
# ★★ AND THE SURFACE COMPARISON ALONE WOULD NOT REACH THE RESOLVER. Measured over this library: every
# published member is either a lambda or a value independent of the substrate, and neither
# `builtins.deepSeq` nor a per-member WHNF force enters a lambda — so with the shim's `src` seam
# sealed by a `throw`, a whole-surface force still returns rc 0. The second cell therefore CALLS the
# library over the suite's own workload fixture, which is what carries the force across the argument
# boundary and into the defaults. Driven both ways: seam sealed ⇒ rc 1 at the seam, seam open ⇒
# rc 0. Without that call a wrong pin PATH would be invisible here — `den-hoag-jhsb`'s
# cell-invisible class, which defers the abort to first force rather than raising it at the boundary.
{ genProgram, ... }:
let
  entry = import ../..;
  dispatched = if builtins.isFunction entry then entry { } else entry;

  fixtures = import ./_fixtures/workload.nix { };
in
{
  # The two entry paths are ONE library. `genProgram` is built from ci's flake inputs, `dispatched`
  # from the same `ci/flake.lock` read as data — so this compares the two suppliers of one
  # construction rather than an expression with itself.
  flake.tests.entry.test-the-defaulted-entry-publishes-the-flake-surface = {
    expr = builtins.attrNames dispatched;
    expected = builtins.attrNames genProgram;
  };

  # The defaults are RESOLVED, not merely declared. The call reaches `prelude` and `scope`, both of
  # which this library's ci lock reaches only THROUGH gen-scope, so a name-shaped default would
  # abort here with `attribute 'gen-prelude' missing` instead of passing.
  flake.tests.entry.test-the-defaulted-entry-resolves-its-dependencies-from-its-ci-lock = {
    expr = builtins.deepSeq (dispatched.program {
      declarations = fixtures.growingInclude;
      frozen = [ ];
    }) "resolved";
    expected = "resolved";
  };
}
