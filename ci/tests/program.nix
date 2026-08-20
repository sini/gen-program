# ORACLE O1 — a declaration becomes a program, and THE PROGRAM IS ASSERTED rather than reported.
#
# ★ THE DISTINCTION THIS SUITE EXISTS FOR: that a construction EVALUATED is not evidence that it
# encoded anything. So every rule is asserted term by term — head, positive body, negative body —
# against the encoding the spec states, and the atom set with it.
#
# ★★ AND THE ASSERTION IS SHOWN TO DISCRIMINATE, IN THE SAME RUN. The mutant is the identical
# declaration set with the NEGATION REMOVED and nothing else changed. If the assertion below
# passed on both, it would be measuring that a program was built and not what is in it — which is
# the failure mode the whole oracle is written against. A control that cannot fail measures
# nothing.
#
# ★ WHAT THIS SUITE DOES NOT CLAIM (spec R§3.1): that solving this program reproduces den v1's
# OUTCOME. That is a parity claim, its instrument is the v1 differential at rung granularity, and
# that instrument does not exist. This is an ENCODING claim and stops there.
{
  genProgram,
  prelude,
  scope,
  ...
}:
let
  fixtures = import ./_fixtures/workload.nix { };

  built = genProgram.program {
    declarations = fixtures.growingInclude;
    frozen = [ ];
  };

  mutant = genProgram.program {
    declarations = fixtures.growingIncludeWithoutNegation;
    frozen = [ ];
  };

  # The encoding the spec states, written out rather than computed from the thing under test: a
  # fixture derived from the construction agrees with it by construction and asserts nothing.
  expectedRules = [
    {
      head = "guard:B";
      pos = [ ];
      neg = [ ];
    }
    {
      head = "member:X";
      pos = [ "guard:B" ];
      neg = [ ];
    }
    {
      head = "guard:A";
      pos = [ "member:X" ];
      neg = [ "excluded:X" ];
    }
    {
      head = "member:Y";
      pos = [ "guard:A" ];
      neg = [ ];
    }
  ];

  # The Herbrand base, in the program's declaration order: heads first, then each rule's positive
  # then negative body. An atom's position is where it was first written.
  expectedAtoms = [
    "guard:B"
    "member:X"
    "guard:A"
    "member:Y"
    "excluded:X"
  ];
in
{
  flake.tests.program = {
    # ── THE ENCODING, TERM BY TERM ──
    test-the-declarations-become-exactly-these-rules = {
      expr = built.rules;
      expected = expectedRules;
    };

    test-the-herbrand-base-is-closed-over-every-atom-any-rule-mentions = {
      expr = built.atoms;
      expected = expectedAtoms;
    };

    # An atom no rule can derive is IN the base and FALSE by the model, rather than absent from it
    # — which is what makes `verdict` total and an unmentioned membership a decided one.
    test-a-negated-atom-no-rule-heads-is-in-the-base = {
      expr = prelude.elem "excluded:X" built.atoms;
      expected = true;
    };

    # The negated literal lands in `neg`. A translation that dropped it, or that put it in `pos`,
    # would build a program whose model is a different question.
    test-the-negated-literal-lands-in-neg-and-not-in-pos = {
      expr = {
        neg = (prelude.elemAt built.rules 2).neg;
        pos = (prelude.elemAt built.rules 2).pos;
      };
      expected = {
        neg = [ "excluded:X" ];
        pos = [ "member:X" ];
      };
    };

    # A declaration with neither body is a FACT — `mkRule`'s own base case, not an omission.
    test-a-declaration-with-neither-body-is-a-fact = {
      expr = prelude.elemAt built.rules 0;
      expected = {
        head = "guard:B";
        pos = [ ];
        neg = [ ];
      };
    };

    # ── THE MUTANT ARM, WHICH MUST FAIL THE SAME ASSERTION ──
    test-control-the-mutant-without-the-negation-is-rejected-by-the-same-assertion = {
      expr = mutant.rules == expectedRules;
      expected = false;
    };

    # And it is rejected for the RIGHT reason: the mutant is a well-formed program that differs in
    # exactly the negative body. Without this the cell above would also pass against a mutant that
    # failed to construct at all.
    test-control-the-mutant-differs-from-the-clean-arm-only-in-the-negative-body = {
      expr = map (r: r.neg) mutant.rules;
      expected = [
        [ ]
        [ ]
        [ ]
        [ ]
      ];
    };

    test-control-the-mutants-heads-and-positive-bodies-are-unchanged = {
      expr = map (r: {
        inherit (r) head pos;
      }) mutant.rules;
      expected = map (r: {
        inherit (r) head pos;
      }) expectedRules;
    };

    # ── THE PROGRAM IS gen-scope's OWN VALUE, UNWRAPPED ──
    # Under the retired boundary construction this had to be a record: the library's minted atoms
    # travelled beside the program so the reporting filter could subtract them again. With no
    # minted atoms there is nothing to carry, so the wrapper is gone and what comes back is the
    # substrate's value itself — asserted here as an exact field set, because a wrapper creeping
    # back is a second shape in front of a consumer.
    test-the-construction-returns-the-substrates-own-program-value = {
      expr = prelude.sort (a: b: a < b) (prelude.attrNames built);
      expected = prelude.sort (a: b: a < b) (
        prelude.attrNames (scope.mkProgram { rules = [ { head = "x"; } ]; })
      );
    };

    # And every atom in it is a string the caller wrote. There is no minter left to exempt.
    test-every-atom-in-the-base-is-one-the-declarations-wrote = {
      expr = built.atoms;
      expected = expectedAtoms;
    };
  };
}
