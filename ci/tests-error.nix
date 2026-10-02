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
    "gen-program: ${named} is not in the frozen set of relata that strictly earlier passes settled, so it does not resolve — a same-pass reference and a root relatum both reach this refusal by that one path, and neither is named as a cycle because a stratum's in-flight output is not nameable from inside it";

  # The two withheld answers on the resolved relation. Each is a FIELD that refuses rather than a
  # field that is absent, so what a consumer meets is a sentence naming the membership and the
  # reason — not a missing attribute naming nothing.
  resolved =
    complete:
    (genProgram.model {
      prior = null;
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

  # `ruleEdges` over a model solved from the same labelled declarations, handed to `program` unstripped.
  ab = [
    "a"
    "b"
  ];
  modelOf =
    complete: declarations:
    genProgram.model {
      program = genProgram.program {
        inherit declarations;
        frozen = ab;
      };
      interpretation = [ ];
      prior = null;
      inherit complete;
    };
  edgesAt =
    complete: declarations:
    genProgram.ruleEdges {
      inherit declarations;
      model = modelOf complete declarations;
    };
in
{
  flake.testsError = {
    # ── THE IDENTIFIER DOORS (den-hoag-bkdkg) ──
    # A record where a name goes — the node VALUE in place of its identifier — used to be admitted by
    # `declaration` and abort past `tryEval` in `program`/`unresolvedRelata`. It is now refused at the
    # one door all three normalise through, by that door's name, and the frozen set's own entries at
    # `unresolvedRelata`. A declaration is read through `.head` so the refusal must reach a caller
    # forcing one field.
    test-declaration-refuses-a-record-head = {
      expr =
        (genProgram.declaration {
          head = {
            name = "a";
          };
          relata = [ ];
        }).head;
      expectedError.msg = exactly "gen-program.declaration: the head is a set, expected a node identifier (a string)";
    };
    test-declaration-refuses-a-record-relatum = {
      expr =
        (genProgram.declaration {
          head = "h";
          relata = [ { name = "a"; } ];
        }).head;
      expectedError.msg = exactly "gen-program.declaration: an entry of relata is a set, expected a node identifier (a string)";
    };
    test-declaration-refuses-a-record-body-atom = {
      expr =
        (genProgram.declaration {
          head = "h";
          neg = [ { name = "a"; } ];
          relata = [ ];
        }).head;
      expectedError.msg = exactly "gen-program.declaration: an entry of neg is a set, expected a node identifier (a string)";
    };
    test-declaration-refuses-relata-that-are-not-a-list = {
      expr =
        (genProgram.declaration {
          head = "h";
          relata = "x";
        }).head;
      expectedError.msg = exactly "gen-program.declaration: relata is a string, expected a list of node identifiers (strings)";
    };
    test-program-refuses-a-record-relatum-at-the-declaration = {
      expr = genProgram.program {
        declarations = [
          {
            head = "h";
            relata = [ { name = "a"; } ];
          }
        ];
        frozen = [ "x" ];
      };
      expectedError.msg = exactly "gen-program.declaration: an entry of relata is a set, expected a node identifier (a string)";
    };
    test-unresolvedRelata-refuses-a-record-in-the-frozen-set = {
      expr = genProgram.unresolvedRelata {
        declarations = [
          {
            head = "h";
            relata = [ "x" ];
          }
        ];
        frozen = [ { name = "a"; } ];
      };
      expectedError.msg = exactly "gen-program.unresolvedRelata: an entry of the frozen set is a set, expected a node identifier (a string)";
    };

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
      expectedError.msg = exactly "gen-program: the membership 'x' is UNDEFINED — the well-founded model's third truth value, neither true nor false, which this relation carries rather than collapsing. Read `flag` and handle 'U'; `included` has no answer to give here";
    };

    test-a-negative-answer-on-a-growing-relation-is-delayed-by-name = {
      expr = ((resolved false).resolve "not-derived-here").included;
      expectedError.msg = exactly "gen-program: the membership 'not-derived-here' is not derived at this pass, but the relation is still growing (complete = false), so a NEGATIVE answer is not yet sound — a later pass may derive it. van Antwerpen et al. 2018 §4.3 delays such a query rather than answering it; read `flag` and handle 'P'";
    };

    # ── THE DOOR-CHECK BYTES (den-hoag-7gp66 P1) — R6's naming, pinned per door. `ci/tests/door-
    # checks.nix` pins that each door's violations are CATCHABLE; a boolean cannot see WHICH
    # refusal fired, so WHICH is pinned here, one golden per door.
    test-unresolvedRelata-missing-required-field-message = {
      expr = genProgram.unresolvedRelata { declarations = [ ]; };
      expectedError.msg = exactly "gen-program.unresolvedRelata: required field 'frozen' is missing (required: 'declarations', 'frozen') (in prelude.checkRequired)";
    };
    test-program-missing-required-field-message = {
      expr = genProgram.program { declarations = [ ]; };
      expectedError.msg = exactly "gen-program.program: required field 'frozen' is missing (required: 'declarations', 'frozen') (in prelude.checkRequired)";
    };
    test-body-missing-required-field-message = {
      expr = genProgram.body { name = "x"; };
      expectedError.msg = exactly "gen-program.body: required field 'clauses' is missing (required: 'name', 'clauses', 'declared') (in prelude.checkRequired)";
    };
    test-adjudicate-missing-required-field-message = {
      expr = genProgram.adjudicate {
        program = genProgram.program {
          declarations = [ ];
          frozen = [ ];
        };
        model = null;
      };
      expectedError.msg = exactly "gen-program.adjudicate: required field 'interpretation' is missing (required: 'program', 'model', 'interpretation') (in prelude.checkRequired)";
    };

    # ── THE NATIVE-ELLIPSIS DOOR-CHECK BYTES (den-hoag-7gp66 P1, arm (C)) ──
    # `declaration`, `model`, `mkModel` and `escape` keep their native required formals — a missing
    # one still aborts the evaluator's own uncatchable way, untested here — and gain `...` plus
    # `prelude.checkOptions` over the raw `args`, so an UNKNOWN field is what is named below.
    test-declaration-unknown-field-message = {
      expr = genProgram.declaration {
        head = "h";
        relata = [ ];
        zzqran7f = 1;
      };
      expectedError.msg = exactly "gen-program.declaration: 'zzqran7f' is not an option of this door; the options are closed (accepted: 'head', 'label', 'neg', 'pos', 'relata', 'when') (in prelude.checkOptions)";
    };
    test-model-unknown-field-message = {
      expr = genProgram.model {
        prior = null;
        program = genProgram.program {
          declarations = [ ];
          frozen = [ ];
        };
        interpretation = [ ];
        complete = true;
        zzqran7f = 1;
      };
      expectedError.msg = exactly "gen-program.model: 'zzqran7f' is not an option of this door; the options are closed (accepted: 'complete', 'interpretation', 'prior', 'program') (in prelude.checkOptions)";
    };
    test-mkModel-unknown-field-message = {
      expr = genProgram.mkModel {
        solved = null;
        program = null;
        adjudication = null;
        complete = true;
        zzqran7f = 1;
      };
      expectedError.msg = exactly "gen-program.mkModel: 'zzqran7f' is not an option of this door; the options are closed (accepted: 'adjudication', 'complete', 'program', 'solved') (in prelude.checkOptions)";
    };
    test-escape-unknown-field-message = {
      expr = genProgram.escape {
        name = "x";
        fn = _: { };
        emits = [ ];
        binds = [ ];
        suppresses = [ ];
        zzqran7f = 1;
      };
      expectedError.msg = exactly "gen-program.escape: 'zzqran7f' is not an option of this door; the options are closed (accepted: 'binds', 'emits', 'fn', 'name', 'suppresses') (in prelude.checkOptions)";
    };

    # den-hoag-ea3j4 — the three refusals the multi-pass protocol names.
    test-withheld-negative-support-message = {
      expr =
        (
          (genProgram.model {
            prior = null;
            program = genProgram.program {
              declarations = [
                {
                  head = "r";
                  relata = [ ];
                }
                {
                  head = "a";
                  pos = [ "r" ];
                  neg = [ "b" ];
                  relata = [ ];
                }
              ];
              frozen = [ ];
            };
            interpretation = [ ];
            complete = false;
          }).resolve
            "a"
        ).included;
      expectedError.msg = exactly "gen-program: the membership 'a' is derived at this pass, but its support rests on negation and the relation is still growing (complete = false), so a later pass may still falsify it. van Antwerpen et al. 2018 §4.3 delays such a query rather than answering it; read `flag` and handle 'P'";
    };
    test-omitted-prior-declaration-message = {
      expr = genProgram.model {
        program = genProgram.program {
          declarations = [
            {
              head = "z";
              relata = [ ];
            }
          ];
          frozen = [ ];
        };
        interpretation = [ ];
        complete = true;
        prior = genProgram.model {
          prior = null;
          program = genProgram.program {
            declarations = [
              {
                head = "r";
                relata = [ ];
              }
            ];
            frozen = [ ];
          };
          interpretation = [ ];
          complete = false;
        };
      };
      expectedError.msg = exactly "gen-program.model: this pass's program drops 1 rule(s) of the prior pass, headed 'r' — every pass resubmits every earlier pass's declarations, because a prior pass's verdicts are not rules and a dropped declaration re-derives nothing it settled";
    };
    test-prior-not-a-record-message = {
      expr = genProgram.model {
        program = genProgram.program {
          declarations = [ ];
          frozen = [ ];
        };
        interpretation = [ ];
        complete = true;
        prior = 1;
      };
      expectedError.msg = exactly "gen-program.model: `prior` is not a gen-program result record — pass the previous pass's `model` result, or `prior = null` on the first pass";
    };

    # ── THE SOLVED MODEL'S EDGES ──
    # An edge has no third value. A negative cycle leaves `r:a:b` UNDEFINED, and reading only the
    # included atoms would drop its edge with no error: the refusal is what this cell holds.
    test-rule-edges-refuses-an-undefined-labelled-membership = {
      expr =
        (edgesAt true [
          {
            head = "r:a:b";
            neg = [ "h:a:b" ];
            relata = ab;
            label = "r";
          }
          {
            head = "h:a:b";
            neg = [ "r:a:b" ];
            relata = ab;
          }
        ]).reached;
      expectedError.msg = exactly "gen-program.ruleEdges: 'r:a:b' is UNDEFINED (U); an edge has no third value, so the membership can be carried into the graph neither as an edge nor as its absence, and is refused rather than collapsed. Read its answer through the model's `resolve` and handle 'U'";
    };
    # A negation-free head is served `included = true` under P; the SET still refuses, because its
    # absences are the negatives a growing relation withholds.
    test-rule-edges-refuses-a-growing-relation = {
      expr =
        (edgesAt false [
          {
            head = "r:a:b";
            relata = ab;
            label = "r";
          }
        ]).reached;
      expectedError.msg = exactly "gen-program.ruleEdges: the relation is still growing (complete = false), so an edge set read from it would assert a negative for every absent candidate that a later pass may still falsify; read `reached` from the pass that closes the relation, or one membership's answer through the model's `resolve`";
    };
    test-rule-edges-refuses-a-model-of-other-declarations = {
      expr =
        (genProgram.ruleEdges {
          declarations = [
            {
              head = "r:a:b";
              relata = ab;
              label = "r";
            }
          ];
          model = modelOf true [
            {
              head = "s:a:b";
              relata = ab;
            }
          ];
        }).reached;
      expectedError.msg = exactly "gen-program.ruleEdges: 'r:a:b' is labelled by a declaration that is not a rule of this model; the model was solved from other declarations, so it cannot answer for these";
    };
    # Keyed by head: a conflict is decidable from the declarations, so it refuses in `candidates`
    # with no model at all.
    test-rule-edges-refuses-conflicting-edges-for-one-head = {
      expr =
        (genProgram.ruleEdges {
          declarations = [
            {
              head = "r:x";
              relata = ab;
              label = "r";
            }
            {
              head = "r:x";
              pos = [ "f" ];
              relata = [
                "a"
                "c"
              ];
              label = "r";
            }
          ];
          model = throw "no model was asked for";
        }).candidates;
      expectedError.msg = exactly "gen-program.ruleEdges: 'r:x' is labelled by declarations naming different edges; an edge is a property of the membership, so its declarations must agree on from, to and label";
    };
    test-rule-edges-refuses-a-labelled-declaration-not-relating-two = {
      expr =
        (genProgram.ruleEdges {
          declarations = [
            {
              head = "r:x";
              relata = [
                "a"
                "b"
                "c"
              ];
              label = "r";
            }
          ];
          model = throw "no model was asked for";
        }).candidates;
      expectedError.msg = exactly "gen-program.ruleEdges: 'r:x' (3 relata) carries a label, but an edge relates exactly two relata, from and to";
    };
    test-declaration-refuses-a-label-that-is-not-a-string = {
      expr =
        (genProgram.declaration {
          head = "h";
          relata = ab;
          label = 42;
        }).head;
      expectedError.msg = exactly "gen-program.declaration: the label is a int, expected an edge label (a string) or null";
    };
    test-rule-edges-missing-field-message = {
      expr = genProgram.ruleEdges { declarations = [ ]; };
      expectedError.msg = exactly "gen-program.ruleEdges: required field 'model' is missing (required: 'declarations', 'model') (in prelude.checkRequired)";
    };
  };
}
