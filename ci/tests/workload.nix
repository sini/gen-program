# ORACLE O3 — v1's growing-include workload resolves to a STATED SEMANTICS, not to an iteration cap.
#
# den v1 at `ecaefcb` answers this shape with a budget: the policy enrichment loop caps at
# `maxPolicyIterations = 10` and THROWS, and the conditional drain stops when it stops progressing
# and tombstones what is left. The report states the standard in its own words — v1 "does not
# establish convergence statically — it BOUNDS it and fails at the bound." A budget standing in
# for a convergence condition is the defect class. Here the same declarations are a program and
# the answer is its model.
#
# ★★ TWO ARMS, BOTH ABLE TO FAIL.
#   (i)  PERMUTATION — the same declarations in a different presentation order give the same
#        model. This can genuinely fail: `den-hoag-2qe9` measures v1's answer as ARRIVAL
#        DEPENDENT — "an aspect admitted at iteration k because key k was absent STAYS ADMITTED at
#        the fixpoint where k is present."
#   (ii) PAST THE CAP — a chain longer than v1's bound yields a model rather than a throw.
#
# ★★★ WHAT "THE SAME MODEL" MEANS HERE, STATED BECAUSE THE OBVIOUS ASSERTION IS THE WRONG ONE.
# The reported lists are in the program's DECLARATION ORDER, and a permuted presentation is a
# different declaration order by construction — so comparing the lists would compare
# presentations and fail on a model that is identical. The model is the VERDICT ASSIGNMENT, and
# the assertion is over an attribute set keyed by atom, whose ordering is the evaluator's
# canonical one and carries nothing of the input's. ★ The arming for that choice is the control
# below, which shows the two presentations ARE different inputs: without it, a permutation cell
# could be comparing a fixture with itself and would pass against any engine at all.
#
# ★ AND THIS MEASURES ORDER-INDEPENDENCE, NEVER PARITY (spec R§3.1). That solving reproduces den
# v1's outcome is a different claim with a different instrument, and that instrument does not
# exist.
{
  genProgram,
  prelude,
  ...
}:
let
  fixtures = import ./_fixtures/workload.nix { };

  modelOf =
    declarations:
    genProgram.model {
      built = genProgram.program {
        inherit declarations;
        frozen = [ ];
        carried = [ ];
      };
      complete = true;
    };

  straight = modelOf fixtures.growingInclude;
  permuted = modelOf fixtures.growingIncludePermuted;

  # THE MODEL AS AN ASSIGNMENT, not as a presentation: one verdict per atom, keyed by atom.
  verdictMap = m: atoms: prelude.genAttrs atoms m.verdict;

  atomsOfInterest = [
    "guard:A"
    "guard:B"
    "member:X"
    "member:Y"
    "excluded:X"
  ];

  # ── PAST THE CAP ──
  longChain = modelOf fixtures.longChain;
  # Every link and every emission of the chain, as the fixture spells them.
  chainAtoms =
    prelude.genList (i: "link:${toString i}") (fixtures.capLength + 1)
    ++ prelude.genList (i: "emitted:${toString i}") fixtures.capLength;
in
{
  flake.tests.workload = {
    # ── THE CHAIN v1's OWN TEST COMMENT DESCRIBES ──
    # Guard A depends on member X, which enters only because guard B passed and emitted it; and A
    # negates X's exclusion, which nothing derives. Under a stated semantics the whole chain
    # settles and the negation is decided rather than iterated at.
    test-the-measured-growing-include-chain-settles-through-the-negation = {
      expr = verdictMap straight atomsOfInterest;
      expected = {
        "guard:B" = "true";
        "member:X" = "true";
        "guard:A" = "true";
        "member:Y" = "true";
        "excluded:X" = "false";
      };
    };

    # Nothing in this workload is contested: the shape needs a semantics, and having one it
    # settles. An engine that answered UNDEFINED wherever a negation appeared would fail here.
    test-the-workload-is-settled-rather-than-contested = {
      expr = straight.undefinedAtoms;
      expected = [ ];
    };

    # ── ARM (i): PERMUTATION ──
    test-a-different-presentation-order-gives-the-same-model = {
      expr = verdictMap permuted atomsOfInterest;
      expected = verdictMap straight atomsOfInterest;
    };

    # THE ARMING. The two presentations are genuinely different inputs — their Herbrand bases are
    # in different orders — so the cell above is comparing two constructions and not one fixture
    # with itself.
    test-control-the-two-presentations-are-genuinely-different-inputs = {
      expr =
        (modelOf fixtures.growingInclude).trueAtoms == (modelOf fixtures.growingIncludePermuted).trueAtoms;
      expected = false;
    };

    # And the difference is presentation ONLY: the same atoms, differently ordered.
    test-control-the-permutation-changes-order-and-not-membership = {
      expr = prelude.sort (a: b: a < b) permuted.trueAtoms;
      expected = prelude.sort (a: b: a < b) straight.trueAtoms;
    };

    # ── ARM (ii): PAST v1's CAP ──
    # Fifteen links, where v1's policy-enrichment loop caps at ten and throws on the eleventh.
    test-a-chain-longer-than-v1s-cap-yields-a-model = {
      expr = prelude.length longChain.trueAtoms;
      expected = prelude.length chainAtoms;
    };

    test-every-link-past-the-cap-is-derived = {
      expr = prelude.all (a: longChain.verdict a == "true") chainAtoms;
      expected = true;
    };

    # The cell above is a claim about a chain that is actually longer than the bound it is named
    # for, so the length is asserted rather than trusted to the fixture's name.
    test-control-the-chain-really-is-longer-than-v1s-bound-of-ten = {
      expr = fixtures.capLength > 10;
      expected = true;
    };

    test-the-long-chain-converged = {
      expr = longChain.converged;
      expected = true;
    };
  };
}
