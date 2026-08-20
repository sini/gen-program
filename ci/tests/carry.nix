# THE PASS BOUNDARY — a prior pass's verdicts crossing as an INTERPRETATION.
#
# This suite is the reason the parameter exists. The boundary used to be a two-rule gadget per
# contested atom, and the gadget made a carried atom FREELY SUPPORTED in every candidate containing
# it — so a program with NO stable model acquired one at the boundary, and on a recurring
# declaration set the coherence adjudication flipped REFUSED → ADMITTED at the first pass and never
# returned. The channel is the repair: a prior pass's verdicts are not rules.
#
# ★★ WHAT IS ARMED HERE AND WHAT IS ARMED NEXT DOOR, STATED SO THE COVERAGE IS READABLE.
# The two operator defects — `U` reaching the UNDERESTIMATE (the mirror), and `U` subtracted from
# it (pinning) — are defects of gen-scope's construction, and gen-scope arrives here as a LOCKED
# FLAKE INPUT: a defective engine is not constructible from this repository. They are armed in
# `gen-scope/ci/tests/interpretation.nix`, on the four-subject table that shows each is INVISIBLE
# on the other's subject. What this suite arms is the BOUNDARY: the outcomes a consumer sees, and
# the collapse control that demonstrates the defect the parameter prevents actually occurring.
{
  genProgram,
  prelude,
  ...
}:
let
  d = r: r // { relata = [ ]; };

  carry = verdict: atoms: map (atom: { inherit atom verdict; }) atoms;
  undef = carry "undefined";
  true' = carry "true";

  modelOf =
    declarations: interpretation:
    genProgram.model {
      program = genProgram.program {
        inherit declarations;
        frozen = [ ];
      };
      inherit interpretation;
      complete = true;
    };

  # ── VGRS EXAMPLE 5.3's `P2` — the paper says in as many words "Hence P2 has no stable model" ──
  p2 = [
    (d {
      head = "p";
      neg = [ "p" ];
    })
  ];

  # `P2` beside an even loop. With `p` carried TRUE the interpreted model is still PARTIAL, so the
  # stability search actually RUNS — which is what makes this fixture able to tell a seeded
  # predicate from an unseeded one. On `P2` alone a TRUE carry gives a TOTAL model, the
  # short-circuit answers before the predicate is reached, and the arm discriminates nothing.
  p2partial = p2 ++ [
    (d {
      head = "a";
      neg = [ "b" ];
    })
    (d {
      head = "b";
      neg = [ "a" ];
    })
  ];

  # ── THE RECURRING DECLARATION SET: identical declarations at every pass, each carrying the
  # previous pass's undefined atoms. This is the fixture the gate measured FLIPPING.
  recurring = p2 ++ [
    (d {
      head = "reader";
      pos = [ "p" ];
    })
  ];

  passes =
    n:
    let
      step =
        acc: _:
        let
          m = modelOf recurring (undef acc.contested);
        in
        {
          contested = m.undefinedAtoms;
          outcomes = acc.outcomes ++ [ m.adjudication.outcome ];
          models = acc.models ++ [ m ];
        };
    in
    prelude.foldl' step {
      contested = [ ];
      outcomes = [ ];
      models = [ ];
    } (prelude.genList (i: i) n);

  threePasses = passes 3;

  # ── O3's SUBJECTS ──
  pureCarry = modelOf [ ] (undef [ "x" ]);
  pureCarryEmpty = modelOf [ ] [ ];

  reader = [
    (d {
      head = "z";
      pos = [ "a" ];
    })
  ];
  carriedForward = modelOf reader (undef [ "a" ]);
  suppressed = modelOf reader [ ];

  # ── O8's SUBJECT: the next pass DERIVES the carried atom from a settled body ──
  determined = modelOf (
    reader
    ++ [
      (d { head = "settled"; })
      (d {
        head = "a";
        pos = [ "settled" ];
      })
    ]
  ) (undef [ "a" ]);
in
{
  flake.tests.carry = {
    # ══ THE COMMISSIONED ORACLE ══
    # The recurring set holds REFUSED at pass 1 and at every pass after. Under the retired boundary
    # this read [ "refused", "admitted", "admitted" ].
    test-the-recurring-declaration-set-holds-refused-at-every-pass = {
      expr = threePasses.outcomes;
      expected = [
        "refused"
        "refused"
        "refused"
      ];
    };

    # ★ THE SUBJECT CONTROL: pass 1's model is genuinely PARTIAL and the search actually ran.
    # Without it the cell above could be reading a fixture that never reached the criterion.
    test-control-the-first-pass-is-partial-and-searched = {
      expr =
        let
          m = prelude.head threePasses.models;
        in
        {
          inherit (m) undefinedAtoms;
          searched = m.adjudication.searched;
          contested = m.adjudication.contested;
        };
      expected = {
        undefinedAtoms = [
          "p"
          "reader"
        ];
        searched = true;
        contested = 2;
      };
    };

    # ★ AND THE BOUNDARY REALLY CARRIES SOMETHING, so the later passes are not pass 1 repeated with
    # an empty interpretation.
    test-control-the-boundary-actually-carries-something = {
      expr = threePasses.contested;
      expected = [
        "p"
        "reader"
      ];
    };

    # ★ THE MECHANISM CONTROL, on a PARTIAL-model fixture: the same shape with a carried atom
    # supplied as TRUE comes back ADMITTED. Without an arm that reads `admitted`, every cell above
    # would pass against an adjudication that refuses everything.
    test-control-a-true-carry-on-a-partial-fixture-is-admitted = {
      expr =
        let
          a = (modelOf p2partial (true' [ "p" ])).adjudication;
        in
        {
          inherit (a) outcome searched;
        };
      expected = {
        outcome = "admitted";
        searched = true;
      };
    };

    # ★★ AND THAT ARM IS WHAT SEPARATES A SEEDED STABILITY PREDICATE FROM AN UNSEEDED ONE, which
    # is why `searched` is asserted beside the outcome: a fixture whose interpreted model is TOTAL
    # short-circuits through Corollary 5.6 and never reaches the predicate, so such an arm passes
    # identically against a build that never seeds.
    test-control-the-true-arms-fixture-is-partial-rather-than-short-circuited = {
      expr = (modelOf p2partial (true' [ "p" ])).adjudication.contested > 0;
      expected = true;
    };

    # ★ THE FREE SAFETY THEOREM, MADE RUNNABLE. The criterion is evaluated on
    # `P′ = P ∪ facts(Pos(I))`, which is a function of the program and the interpretation's TRUE
    # atoms ALONE — so adding further UNDEFINED carries cannot move the answer in either direction.
    test-adding-undefined-carries-does-not-move-the-outcome = {
      expr = map (extra: (modelOf recurring (undef extra)).adjudication.outcome) [
        [ ]
        [ "p" ]
        [
          "p"
          "reader"
        ]
        [
          "p"
          "reader"
          "an-atom-no-rule-mentions"
        ]
      ];
      expected = [
        "refused"
        "refused"
        "refused"
        "refused"
      ];
    };

    # ══ THE PINNED BOUNDARY CELL'S TWO READINGS COLLAPSE TO ONE ══
    # This cell used to pin `carried = [ ]` ⇒ refused BESIDE `carried = [ "p" ]` ⇒ admitted, and
    # that difference WAS the measured defect. Under the parameter both are REFUSED, and the
    # collapse is what is asserted.
    test-the-two-boundary-readings-of-P2-collapse-to-refused = {
      expr = {
        without = (modelOf p2 [ ]).adjudication.outcome;
        withUndefinedCarry = (modelOf p2 (undef [ "p" ])).adjudication.outcome;
      };
      expected = {
        without = "refused";
        withUndefinedCarry = "refused";
      };
    };

    # ★ THE THIRD READING, WHICH KEEPS THE COLLAPSE FROM BEING "IT REFUSES EVERYTHING": the same
    # atom carried TRUE on the PARTIAL fixture is ADMITTED, because `P′ = P2 ∪ { p. }` is a
    # genuinely different program in which `p` is externally true and `p :- not p` is satisfied.
    # **That is exactly the distinction the retired boundary could not draw.**
    test-the-true-carry-reading-is-admitted-and-that-is-the-distinction = {
      expr = (modelOf p2partial (true' [ "p" ])).adjudication.outcome;
      expected = "admitted";
    };

    # ══ UNDEFINED SURVIVES THE BOUNDARY ══
    # Including the PURE-CARRY case, where this pass's program does not mention the atom at all.
    # That needs the engine's extended base: without it the atom is absent from the enumerations
    # and only `verdict`'s totality would answer.
    test-a-pure-carry-is-undefined-and-is-reported = {
      expr = {
        verdict = pureCarry.verdict "x";
        enumerated = pureCarry.undefinedAtoms;
      };
      expected = {
        verdict = "undefined";
        enumerated = [ "x" ];
      };
    };

    # ★ THE COLLAPSE CONTROL, AND IT MUST BE DEMONSTRATED TO OCCUR: the identical pass with the
    # EMPTY interpretation returns that atom FALSE. This is the defect the parameter prevents, and
    # a fixture where it does not occur has no subject.
    test-control-with-an-empty-interpretation-the-same-atom-collapses-to-false = {
      expr = {
        verdict = pureCarryEmpty.verdict "x";
        enumerated = pureCarryEmpty.undefinedAtoms;
      };
      expected = {
        verdict = "false";
        enumerated = [ ];
      };
    };

    # And it propagates: a rule whose POSITIVE body reads a carried-undefined atom is itself
    # undefined. ★ The retired boundary reached this answer only because its manufactured atom was
    # a real atom; the parameter reaches it through the overestimate's SEEDED fixpoint, which is
    # what makes carried undefinedness propagate through a positive body rather than through
    # negation alone.
    test-a-positive-reader-of-a-carried-atom-is-undefined-too = {
      expr = carriedForward.undefinedAtoms;
      expected = [
        "z"
        "a"
      ];
    };

    test-control-the-same-reader-with-no-carry-is-false = {
      expr = {
        inherit (suppressed) undefinedAtoms falseAtoms;
      };
      expected = {
        undefinedAtoms = [ ];
        falseAtoms = [
          "z"
          "a"
        ];
      };
    };

    # ══ THE OVER-PINNING ARM ══
    # Where this pass carries a positive rule deriving the atom from a settled body, it comes back
    # TRUE. The carry supplies undefinedness only in the ABSENCE of other information; one that
    # froze an atom new information settles would be a fourth value wearing the third one's name.
    test-a-carry-does-not-pin-an-atom-this-pass-derives = {
      expr = determined.verdict "a";
      expected = "true";
    };

    test-control-the-determined-arm-settles-its-reader-too = {
      expr = {
        inherit (determined) trueAtoms undefinedAtoms;
      };
      expected = {
        trueAtoms = [
          "z"
          "settled"
          "a"
        ];
        undefinedAtoms = [ ];
      };
    };

    # ══ THE RETIREMENT, MEASURED AT THE BOUNDARY AND NOT ONLY ON THE ROSTER ══
    # No atom in any reported list is one this library introduced — and that is now true because
    # there is no minter, not because a filter removed them.
    test-every-reported-atom-is-one-the-caller-wrote = {
      expr =
        let
          reported = carriedForward.trueAtoms ++ carriedForward.undefinedAtoms ++ carriedForward.falseAtoms;
        in
        prelude.sort (a: b: a < b) reported;
      expected = [
        "a"
        "z"
      ];
    };

    # ★ The control for that absence: the same predicate over a set that DOES contain a foreign
    # atom returns it. An absence over a predicate that could not have matched is not an absence.
    test-control-the-same-predicate-finds-a-foreign-atom-when-there-is-one = {
      expr =
        let
          authored = [
            "a"
            "z"
          ];
          reported =
            carriedForward.trueAtoms
            ++ carriedForward.undefinedAtoms
            ++ carriedForward.falseAtoms
            ++ [ "gen-program::a" ];
        in
        prelude.filter (x: !(prelude.elem x authored)) reported;
      expected = [ "gen-program::a" ];
    };
  };
}
