# ORACLE O6 — THE RULED CRITERION'S DISPOSITION IS A REQUIRED FIELD, NEVER A SILENCE.
#
# ADR-0020 makes stable-model existence the refusal oracle. Before this library nothing evaluated
# it, so every solved program was un-adjudicated by the criterion that governs it and silence read
# as admission. What the spec fixes REGARDLESS of which arm the fork took is the FIELD and its
# REQUIREDNESS; what the ruling then settled is that the criterion is BUILT and runs under a
# derived budget, past which the field carries NOT-EVALUATED.
#
# ★★★ THE ORACLE IS REWRITTEN FROM THE OBVIOUS ONE, AND THE ORIGINAL COULD NOT BE RUN. Its control
# was "a program that DOES have a stable model carries no such statement" — which requires DECIDING
# stable-model existence, the very NP-complete question whose absence the oracle existed to report.
# An oracle whose control needs the unbuilt instrument measures nothing.
#
# ★★ SO THE CONTROLS DISCRIMINATE THE CHANNEL, NOT THE PROGRAM, ON THREE AXES:
#   (i)   INDEPENDENCE — the field is present on a result whose `provenance` is EMPTY and on one
#         whose `provenance` is POPULATED, proving it is not `provenance` under another name.
#   (ii)  REQUIREDNESS — the formal carries no default, so a construction that omits it does not
#         apply. ★ The evaluator's refusal for a missing required argument is UNCATCHABLE —
#         `tryEval` does not contain it, which `ci/bench/requiredness-probe.nix` exhibits and the
#         README records — so what a CELL can read is the formal itself, through
#         `builtins.functionArgs`. The mutant beside it is a constructor with the field DEFAULTED,
#         which reads `true` in the same call: without it the cell would pass against any reading
#         at all.
#   (iii) NOT A SIDE CHANNEL — the statement survives being carried across an evaluation boundary
#         AS DATA. Its mutant is the same result with the statement moved to `builtins.trace`,
#         which is exactly the shape a consumer can drop: a printed warning goes to stderr, which
#         the evaluation cache swallows after the first run.
{
  genProgram,
  prelude,
  scope,
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

  # A TOTAL well-founded model: nothing contested.
  total = modelOf fixtures.growingInclude;

  # A PARTIAL model whose program HAS stable models — Van Gelder, Ross & Schlipf 1991's `P1`,
  # whose two stable models are `{a}` and `{b}`.
  hasStable = modelOf [
    {
      head = "a";
      neg = [ "b" ];
      relata = [ ];
    }
    {
      head = "b";
      neg = [ "a" ];
      relata = [ ];
    }
  ];

  # A PARTIAL model whose program has NO stable model — the same paper's `P2`, `p :- not p`, of
  # which it says in as many words: "Hence P2 has no stable model."
  noStable = modelOf [
    {
      head = "p";
      neg = [ "p" ];
      relata = [ ];
    }
  ];

  # PAST THE BUDGET: one contested atom more than the derived figure admits. The count is read
  # FROM the library, so this fixture tracks a re-derivation instead of going stale beside it.
  overBudget = modelOf (
    prelude.genList (i: {
      head = "q${toString i}";
      neg = [ "q${toString i}" ];
      relata = [ ];
    }) (genProgram.stableModelBudget.contested + 1)
  );

  # ── AXIS (i): the two `provenance` states, from the engine's own verified figure ──
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
  provenancePopulated = modelOf (chainOf (scope.verifiedDepth.depth + 1));
  provenanceEmpty = modelOf (chainOf 32);

  # ── AXIS (ii): the mutant constructor, with the field DEFAULTED ──
  mutantConstructor =
    {
      solved,
      authored,
      adjudication ? null,
      complete,
    }:
    {
      inherit
        solved
        authored
        adjudication
        complete
        ;
    };

  # ── AXIS (iii): the data boundary, and the side channel beside it ──
  crossBoundary = v: builtins.fromJSON (builtins.toJSON v);
  # The result's DATA, which is what crosses a boundary at all. `verdict` and `resolve` are
  # functions and no function crosses one — that is a property of the boundary and not of this
  # field, so both arms below are taken over the same projection and the comparison is about the
  # CHANNEL rather than about what `toJSON` happens to accept.
  dataOf =
    m:
    removeAttrs m [
      "verdict"
      "resolve"
    ];
  # The statement moved OFF the value and onto a channel a consumer can drop: a printed emission
  # goes to stderr, which the evaluation cache swallows after the first run.
  sideChannelled = builtins.trace total.adjudication.reason (
    removeAttrs (dataOf total) [
      "adjudication"
    ]
  );
in
{
  flake.tests.adjudication = {
    # ── THE FIELD IS ON EVERY RESULT, AND SAYS WHAT IT IS ABOUT ──
    test-every-result-carries-the-adjudication-field = {
      expr = map (m: m ? adjudication) [
        total
        hasStable
        noStable
        overBudget
        provenancePopulated
        provenanceEmpty
      ];
      expected = [
        true
        true
        true
        true
        true
        true
      ];
    };

    test-the-field-names-adr-0020s-criterion-on-every-result = {
      expr = prelude.unique (
        map (m: m.adjudication.criterion) [
          total
          hasStable
          noStable
          overBudget
        ]
      );
      expected = [ genProgram.stableModelCriterion ];
    };

    # Every outcome is a member of the closed vocabulary. A widened outcome fails here rather than
    # passing silently.
    test-every-outcome-is-a-member-of-the-published-vocabulary = {
      expr = prelude.all (m: prelude.elem m.adjudication.outcome genProgram.adjudicationOutcomes) [
        total
        hasStable
        noStable
        overBudget
      ];
      expected = true;
    };

    # ── THE BOUNDED ARM, AS RULED ──
    # A TOTAL well-founded model IS the unique stable model, so coherence is certified by the
    # value path and no search runs. Van Gelder, Ross & Schlipf 1991, Corollary 5.6.
    test-a-total-model-is-admitted-by-the-short-circuit-without-searching = {
      expr = {
        inherit (total.adjudication) outcome searched contested;
      };
      expected = {
        outcome = "admitted";
        searched = false;
        contested = 0;
      };
    };

    test-the-short-circuit-cites-the-result-it-rests-on = {
      expr = total.adjudication.ground;
      expected = "Van Gelder, Ross & Schlipf 1991, Corollary 5.6";
    };

    # A PARTIAL model does NOT short-circuit: the converse of Corollary 5.6 is not available, so
    # the search genuinely runs. This is the arm that would vanish if the short-circuit were
    # written as "partial ⇒ refuse".
    test-a-partial-model-with-a-stable-model-is-admitted-by-searching = {
      expr = {
        inherit (hasStable.adjudication) outcome searched contested;
      };
      expected = {
        outcome = "admitted";
        searched = true;
        contested = 2;
      };
    };

    # ★ THE REFUSAL, WHICH IS THE WHOLE POINT OF BUILDING THE ORACLE. Corollary 5.7 bounds every
    # stable model to the searched candidate space, so an exhausted walk is a DECISION and not a
    # sample.
    test-a-program-with-no-stable-model-is-refused-by-the-criterion = {
      expr = {
        inherit (noStable.adjudication) outcome searched;
      };
      expected = {
        outcome = "refused";
        searched = true;
      };
    };

    # PAST THE BUDGET the field carries NOT-EVALUATED — a named outcome. It states an ABSENCE of
    # adjudication and is never an admission.
    test-past-the-budget-the-field-carries-not-evaluated = {
      expr = {
        inherit (overBudget.adjudication) outcome searched;
        overBudget = overBudget.adjudication.contested > genProgram.stableModelBudget.contested;
      };
      expected = {
        outcome = "not-evaluated";
        searched = false;
        overBudget = true;
      };
    };

    # The budget is never a bare number: it carries the derivation that produced it, the fixture
    # families that derivation reads, and the environment terms it holds under.
    test-the-budget-carries-its-derivation-and-terms = {
      expr = prelude.sort (a: b: a < b) (prelude.attrNames genProgram.stableModelBudget);
      expected = [
        "contested"
        "derivation"
        "environment"
        "fixtures"
        "reDerivationOwedOn"
      ];
    };

    # ── AXIS (i): INDEPENDENCE FROM `provenance` ──
    test-control-the-field-is-present-on-both-provenance-states = {
      expr = {
        populated = provenancePopulated.provenance != [ ] && provenancePopulated ? adjudication;
        empty = provenanceEmpty.provenance == [ ] && provenanceEmpty ? adjudication;
      };
      expected = {
        populated = true;
        empty = true;
      };
    };

    # And it does not TRACK `provenance`: the two results above differ in their stamp and agree in
    # their adjudication, which is what "two fields, two disciplines" means when it is measured.
    test-control-the-two-provenance-states-carry-the-same-adjudication = {
      expr = provenancePopulated.adjudication == provenanceEmpty.adjudication;
      expected = true;
    };

    # ── AXIS (ii): REQUIREDNESS ──
    test-the-adjudication-formal-carries-no-default = {
      expr = (builtins.functionArgs genProgram.mkModel).adjudication;
      expected = false;
    };

    test-control-a-constructor-with-the-field-defaulted-reads-otherwise = {
      expr = (builtins.functionArgs mutantConstructor).adjudication;
      expected = true;
    };

    # Every formal of the real constructor is required, so there is no field of the result record
    # a construction can silently omit.
    test-control-no-formal-of-the-constructor-carries-a-default = {
      expr = builtins.functionArgs genProgram.mkModel;
      expected = {
        adjudication = false;
        authored = false;
        complete = false;
        solved = false;
      };
    };

    # ── AXIS (iii): NOT A SIDE CHANNEL ──
    test-the-statement-survives-an-evaluation-boundary-as-data = {
      expr = crossBoundary total.adjudication == total.adjudication;
      expected = true;
    };

    test-control-a-statement-moved-to-a-trace-does-not-survive-that-boundary = {
      expr = (crossBoundary sideChannelled) ? adjudication;
      expected = false;
    };

    # The two arms differ in the CHANNEL and not in the value: the side-channelled mutant carries
    # the same reason text, and it is gone from the data all the same.
    test-control-the-same-projection-with-the-field-left-on-it-does-survive = {
      expr = (crossBoundary (dataOf total)) ? adjudication;
      expected = true;
    };
  };
}
