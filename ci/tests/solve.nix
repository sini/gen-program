# ORACLE O5 — THE RULED ACCEPTANCE: a policy stratum is solved THROUGH THE ENGINE, and ADR-0022's
# benchmark becomes runnable.
#
# ★ THIS IS THE ORACLE THE WHOLE COMMISSION TURNS ON, AND IT RETIRES LAST. ADR-0022's recorded
# exit is armed by BENCHMARK ACCEPTANCE FAILURE. With nothing turning declarations into a program
# and reaching `engine.solve`, that benchmark never runs and the exit can never fire — so the
# confluence commitment was stated and untestable. A consumer is what makes it testable. A plan
# that landed the translation without reaching the solve would have rebuilt the wiring gap one
# layer up.
#
# ★★ THE ARM THAT MAKES THE STAMP MEAN SOMETHING IS THE EMPTY ONE. `provenance` is populated PAST
# the engine's benchmark-verified condensation depth and EMPTY inside it — a field that is always
# populated says nothing about the input that produced it, so without the inside-bound arm the
# stamp is untested and the populated cell alone would pass against a constant.
{
  genProgram,
  scope,
  prelude,
  ...
}:
let
  fixtures = import ./_fixtures/workload.nix { };

  modelOf =
    declarations:
    genProgram.model {
      program = genProgram.program {
        inherit declarations;
        frozen = [ ];
      };
      # These cells are about the un-interpreted case; the interpreted boundary is
      # ci/tests/carry.nix, where the interpretation is the subject rather than a constant.
      interpretation = [ ];
      complete = true;
    };

  # ── THE STRATUM, END TO END ──
  stratum = modelOf fixtures.growingInclude;

  # ── THE BENCHMARK PATH ──
  # A chain of `n` rules is `n + 1` singleton components in a line, so its condensation depth is
  # `n`. The engine's verified figure is read FROM the engine rather than written here: a fixture
  # carrying its own copy of that number would go on passing after the engine re-derived it.
  verified = scope.verifiedDepth.depth;

  chainOf =
    n:
    prelude.genList (i: {
      head = "c${toString i}";
      pos = [ "c${toString (i + 1)}" ];
      relata = [ ];
    }) n
    ++ [
      {
        head = "c${toString n}";
        relata = [ ];
      }
    ];

  pastBound = modelOf (chainOf (verified + 1));
  insideBound = modelOf (chainOf 32);
in
{
  flake.tests.solve = {
    # ── THE RULED ACCEPTANCE ──
    # Declarations went in, `engine.solve` ran, and a model came out. Everything else in this
    # repository is downstream of this cell.
    test-a-stratum-of-declarations-is-solved-through-the-engine = {
      expr = {
        inherit (stratum) trueAtoms falseAtoms undefinedAtoms;
      };
      expected = {
        trueAtoms = [
          "guard:B"
          "member:X"
          "guard:A"
          "member:Y"
        ];
        falseAtoms = [ "excluded:X" ];
        undefinedAtoms = [ ];
      };
    };

    # The result carries the engine's own convergence flag, so a model that did not reach its
    # fixpoint is visible on the value rather than inferable from a cost.
    test-the-solve-converged = {
      expr = stratum.converged;
      expected = true;
    };

    # ── THE BENCHMARK PATH IS EXERCISED ──
    test-an-input-past-the-verified-depth-carries-a-populated-provenance = {
      expr = prelude.length pastBound.provenance;
      expected = 1;
    };

    # And the stamp carries what makes it readable: the depth reached, the verified figure, and
    # the derivation that figure came from. A stamp that said only "exceeded" would name a
    # condition without letting anyone re-derive it.
    test-the-stamp-carries-the-depth-the-verified-figure-and-its-derivation = {
      expr =
        let
          stamp = prelude.head pastBound.provenance;
        in
        {
          depth = stamp.condensationDepth;
          verifiedDepth = stamp.verifiedDepth;
          derivationIsTheEngines = stamp.derivation == scope.verifiedDepth.derivation;
          fixturesAreTheEngines = stamp.fixtures == scope.verifiedDepth.fixtures;
        };
      expected = {
        depth = verified + 1;
        verifiedDepth = verified;
        derivationIsTheEngines = true;
        fixturesAreTheEngines = true;
      };
    };

    # ── THE ARM THAT MAKES THE STAMP MEAN SOMETHING ──
    test-control-an-input-inside-the-bound-carries-an-empty-provenance = {
      expr = insideBound.provenance;
      expected = [ ];
    };

    # The two arms differ in the input rather than in anything else, so the depths are asserted
    # apart from the stamp: without this, both cells could be reading one fixture.
    test-control-the-two-arms-straddle-the-verified-depth = {
      expr = {
        past = pastBound.condensationDepth > verified;
        inside = insideBound.condensationDepth < verified;
      };
      expected = {
        past = true;
        inside = true;
      };
    };

    # Both arms are real models, not merely inputs that produced a stamp.
    test-control-both-benchmark-arms-converged-and-settled-their-chains = {
      expr = {
        past = pastBound.converged && pastBound.undefinedAtoms == [ ];
        inside = insideBound.converged && insideBound.undefinedAtoms == [ ];
      };
      expected = {
        past = true;
        inside = true;
      };
    };
  };
}
