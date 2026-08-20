# ORACLE O2 — the negative cycle gets UNDEFINED, and UNDEFINED is a VALUE rather than a gap.
#
# Gelfond & Lifschitz's second failure mode — `a :- not b`, `b :- not a` — is the shape Apt, Blair
# & Walker's stratified semantics leaves without a meaning at all (their Lemma 1: a program is
# stratified iff its dependency graph carries no cycle containing a negative edge), and it is the
# shape ADR-0020 rules a meaning for. This suite runs it through this library end to end and
# asserts that the third value arrives under its own name.
#
# ★★ THREE CONTROL ARMS, AND THE THIRD IS THE ONE THAT ACTUALLY DISCRIMINATES.
#   (i)  a POSITIVE cycle comes back FALSE — ABW's covered fragment, which must NOT acquire a
#        third value just because the engine has one.
#   (ii) a locally stratified program comes back TOTAL — no undefined atom anywhere.
#   (iii) a program that is NOT locally stratified and whose model is nonetheless PARTIAL: the
#        negative cycle over `{a, b}` PLUS an independent fact `c` and a rule `d :- c`, returning
#        `true = {c, d}` and `undefined = {a, b}` IN THE SAME RESULT.
#
# ★★★ WHY (iii) IS NOT A THIRD HELPING OF THE SAME THING. Arms (i) and (ii) both sit inside ABW's
# covered fragment, so together they cannot distinguish an ATOM-LEVEL model from a BLANKET one: an
# engine that answered "everything undefined" whenever any cycle carried a negative edge would
# pass both. (iii) fails against exactly that engine, and against the opposite one that settles
# everything. It is ADR-0020's granularity ruling — "one contested pair contested while its
# neighbours in the same relation settle" — made runnable.
{
  genProgram,
  ...
}:
let
  solveOf =
    declarations:
    genProgram.model {
      built = genProgram.program {
        inherit declarations;
        frozen = [ ];
        carried = [ ];
      };
      complete = true;
    };

  # THE SUBJECT: the negative two-cycle.
  negativeCycle = solveOf [
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

  # ARM (i): the POSITIVE two-cycle. Nothing supports either atom, so both are FALSE — the
  # unfounded-set half, and the one a derivation-only engine gets wrong by returning nothing.
  positiveCycle = solveOf [
    {
      head = "a";
      pos = [ "b" ];
      relata = [ ];
    }
    {
      head = "b";
      pos = [ "a" ];
      relata = [ ];
    }
  ];

  # ARM (ii): locally stratified — a fact and a negation over something already settled.
  stratified = solveOf [
    {
      head = "p";
      relata = [ ];
    }
    {
      head = "q";
      neg = [ "r" ];
      relata = [ ];
    }
  ];

  # ARM (iii): NOT locally stratified, and the model is PARTIAL rather than blank.
  mixed = solveOf [
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
    {
      head = "c";
      relata = [ ];
    }
    {
      head = "d";
      pos = [ "c" ];
      relata = [ ];
    }
  ];
in
{
  flake.tests.undefined = {
    # ── THE SUBJECT ──
    test-the-negative-cycles-atoms-are-enumerated-as-undefined = {
      expr = negativeCycle.undefinedAtoms;
      expected = [
        "a"
        "b"
      ];
    };

    # The enumeration and the verdict are different surfaces, and a result could carry one without
    # the other. Both are asserted.
    test-the-verdict-answers-undefined-by-name-for-each = {
      expr = map negativeCycle.verdict [
        "a"
        "b"
      ];
      expected = [
        "undefined"
        "undefined"
      ];
    };

    test-the-negative-cycle-settles-nothing-either-way = {
      expr = {
        inherit (negativeCycle) trueAtoms falseAtoms;
      };
      expected = {
        trueAtoms = [ ];
        falseAtoms = [ ];
      };
    };

    # ── ARM (i): ABW's COVERED FRAGMENT MUST NOT ACQUIRE A THIRD VALUE ──
    test-control-a-positive-cycle-comes-back-false-and-not-undefined = {
      expr = {
        inherit (positiveCycle) falseAtoms undefinedAtoms;
      };
      expected = {
        falseAtoms = [
          "a"
          "b"
        ];
        undefinedAtoms = [ ];
      };
    };

    # ── ARM (ii): A LOCALLY STRATIFIED PROGRAM IS TOTAL ──
    test-control-a-locally-stratified-program-carries-no-undefined-atom = {
      expr = stratified.undefinedAtoms;
      expected = [ ];
    };

    test-control-the-stratified-arm-settles-its-atoms-both-ways = {
      expr = {
        inherit (stratified) trueAtoms falseAtoms;
      };
      expected = {
        trueAtoms = [
          "p"
          "q"
        ];
        falseAtoms = [ "r" ];
      };
    };

    # ── ARM (iii): THE ONE THAT SEPARATES AN ATOM-LEVEL MODEL FROM A BLANKET ONE ──
    test-control-a-partial-model-settles-its-neighbours-while-the-cycle-stays-contested = {
      expr = {
        inherit (mixed) trueAtoms undefinedAtoms falseAtoms;
      };
      expected = {
        trueAtoms = [
          "c"
          "d"
        ];
        undefinedAtoms = [
          "a"
          "b"
        ];
        falseAtoms = [ ];
      };
    };

    # ── TOTALITY ──
    # An atom no rule mentions is FALSE, and says so, rather than answering with an absence the
    # caller has to interpret. UNDEFINED is a value this function returns, never a silence it
    # falls into.
    test-the-verdict-on-an-atom-no-rule-mentions-is-false = {
      expr = negativeCycle.verdict "an-atom-this-program-never-heard-of";
      expected = "false";
    };

    # The alternating fixpoint reached its own, and the inner least-model rounds reached theirs.
    # An unconverged result is INVALID rather than slow, and every cell above rests on this one.
    test-every-arm-converged = {
      expr = map (m: m.converged) [
        negativeCycle
        positiveCycle
        stratified
        mixed
      ];
      expected = [
        true
        true
        true
        true
      ];
    };
  };
}
