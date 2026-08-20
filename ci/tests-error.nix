# THE SECOND TEST OUTPUT — cells whose subject is an ERROR MESSAGE, and why they cannot live in
# `flake.tests`.
#
# THAT a construction refuses is a boolean and `tryEval` asserts it; those cells live in the
# suites. WHICH refusal fired is a claim about the message, and `tryEval` returns
# `{ success, value }` and DISCARDS the text — so a suite of booleans alone is equally satisfied by
# a construction with one refusal in it, and a reworded message regresses nothing any cell reads.
# nix-unit's `expectedError` is the assertion for that, and this is where it goes.
#
# ★ WHY A SECOND OUTPUT RATHER THAN A SECOND SUITE. The batch asserter behind `checks.default`
# evaluates `t.expr == t.expected` UNCONDITIONALLY and quantifies over `config.flake.tests` and
# nothing else, so a cell with no `expected` and a throwing `expr` CRASHES that gate rather than
# failing it. Hosting these on `flake.testsError` puts them outside that quantifier while keeping
# them live on the nix-unit path. The split is structural, not conventional: this file is not
# under `./tests`, which is the whole of `testModules`.
#
#   nix-unit --flake ./ci#tests        # the suites
#   nix-unit --flake ./ci#testsError   # these cells
#
# ★★ `expectedError.msg` IS SEARCHED, NOT WHOLE-MATCHED, so a pattern naming a PREFIX of the
# message passes against a message that says something else after it — which would make these
# cells agree with the very rewording they exist to catch. Every pattern below is therefore
# anchored at both ends and built by ESCAPING THE LITERAL TEXT rather than by hand: a hand-written
# pattern is one forgotten backslash away from a metacharacter matching something it was meant to
# spell.
#
# ★★★ AND THE MESSAGES MATTER MORE HERE THAN THEY USUALLY DO, BECAUSE TWO OF THEM ARE THE WHOLE
# CONTENT OF AN ORACLE. O4 asks that a same-pass reference refuse AS AN UNRESOLVED RELATUM and
# NOT as a cycle — a refusal naming a cycle would be a detector for something ADR-0033 rules
# inexpressible. That distinction lives in the text, and this file is where it is held.
{
  genProgram,
  prelude,
  ...
}:
let
  # The message, pinned to the byte. `escapeRegex` is the prelude's own and its metacharacter set
  # is byte-identical to nixpkgs', so what is anchored below is the text as written above it.
  exactly = msg: "^" + prelude.escapeRegex msg + "$";

  build =
    { declarations, frozen }:
    genProgram.program { inherit declarations frozen; };

  declaring = relata: [
    {
      head = "h";
      inherit relata;
    }
  ];

  unresolvedRefusal =
    named:
    "gen-program: ${named} is not in the frozen set of relata that strictly earlier passes settled (ADR-0016 ruling 7), so it does not resolve — a same-pass reference and a root relatum both reach this refusal by that one path, and neither is named as a cycle because a stratum's in-flight output is not nameable from inside it (ADR-0033)";

  # The two withheld answers on the resolved relation. Each is a FIELD that refuses rather than a
  # field that is absent, so what a consumer meets is a sentence naming the membership and the
  # reason — not a missing attribute naming nothing.
  resolved =
    complete:
    (genProgram.model {
      program = genProgram.program {
        declarations = [
          {
            head = "in";
            relata = [ ];
          }
          {
            head = "x";
            neg = [ "y" ];
            relata = [ ];
          }
          {
            head = "y";
            neg = [ "x" ];
            relata = [ ];
          }
        ];
        frozen = [ ];
      };
      interpretation = [ ];
      inherit complete;
    });
in
{
  flake.testsError = {
    # ── O4: THE REFUSAL NAMES THE IDENTIFIER, AND NOT A CYCLE ──
    test-a-same-pass-relatum-refuses-by-naming-the-identifier = {
      expr = build {
        declarations = declaring [ "same-pass:node" ];
        frozen = [ "earlier:node" ];
      };
      expectedError.msg = exactly (unresolvedRefusal "'same-pass:node'");
    };

    # The ROOT reaches the identical sentence, which is what shows the two are ONE mechanism. If
    # the same-pass case had a message of its own it would be a detector after all.
    test-a-root-relatum-refuses-with-the-identical-sentence = {
      expr = build {
        declarations = declaring [ "root" ];
        frozen = [ "earlier:node" ];
      };
      expectedError.msg = exactly (unresolvedRefusal "'root'");
    };

    # Several unresolved relata are named together, in first-occurrence order, so a caller learns
    # every one rather than the first and then the next on a re-run.
    test-several-unresolved-relata-are-all-named = {
      expr = build {
        declarations = declaring [
          "same-pass:node"
          "root"
        ];
        frozen = [ "earlier:node" ];
      };
      expectedError.msg = exactly (unresolvedRefusal "'same-pass:node', 'root'");
    };

    # ── THE THIRD VALUE'S TWO WITHHELD ANSWERS ──
    test-an-undefined-membership-refuses-to-answer-included = {
      expr = ((resolved true).resolve "x").included;
      expectedError.msg = exactly "gen-program: the membership 'x' is UNDEFINED — ADR-0020's third value, which this relation carries rather than collapsing. Read `flag` and handle 'U'; `included` has no answer to give here";
    };

    test-a-negative-answer-on-a-growing-relation-is-delayed-by-name = {
      expr = ((resolved false).resolve "not-derived-here").included;
      expectedError.msg = exactly "gen-program: the membership 'not-derived-here' is not derived at this pass, but the relation is still growing (complete = false), so a NEGATIVE answer is not yet sound — a later pass may derive it. van Antwerpen et al. 2018 §4.3 delays such a query rather than answering it; read `flag` and handle 'P'";
    };
  };
}
