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
  scope,
  ...
}:
let
  # The message, pinned to the byte. `escapeRegex` is the prelude's own and its metacharacter set
  # is byte-identical to nixpkgs', so what is anchored below is the text as written above it.
  exactly = msg: "^" + prelude.escapeRegex msg + "$";

  build =
    { declarations, frozen }:
    genProgram.program frozen declarations;

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
      program =
        genProgram.program
          [ ]
          [
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
      program = genProgram.program ab declarations;
      interpretation = [ ];
      prior = null;
      inherit complete;
    };
  edgesAt = complete: declarations: genProgram.ruleEdges (modelOf complete declarations) declarations;
  # ── the operand-door fixtures: ONE good value per operand, so each cell breaks exactly one ──
  opDecls = [
    {
      head = "r:x";
      relata = ab;
      label = "r";
    }
  ];
  opLabelled = opDecls;
  opProgram = genProgram.program ab opDecls;
  opModel = genProgram.model {
    program = opProgram;
    interpretation = [ ];
    complete = true;
    prior = null;
  };
  opSolved = scope.solve [ ] opProgram;
  opAdj = {
    program = opProgram;
    model = opSolved;
    interpretation = [ ];
  };
  opMk = {
    solved = opSolved;
    program = opProgram;
    adjudication = opModel.adjudication;
    complete = true;
  };
  opModelArgs = {
    program = opProgram;
    interpretation = [ ];
    complete = true;
    prior = null;
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
        (genProgram.declaration { } [ ] {
          name = "a";
        }).head;
      expectedError.msg = exactly "gen-program.declaration: the head is a set, expected a node identifier (a string)";
    };
    test-declaration-refuses-a-record-relatum = {
      expr = (genProgram.declaration { } [ { name = "a"; } ] "h").head;
      expectedError.msg = exactly "gen-program.declaration: an entry of relata is a set, expected a node identifier (a string)";
    };
    test-declaration-refuses-a-record-body-atom = {
      expr = (genProgram.declaration { neg = [ { name = "a"; } ]; } [ ] "h").head;
      expectedError.msg = exactly "gen-program.declaration: an entry of neg is a set, expected a node identifier (a string)";
    };
    test-declaration-refuses-relata-that-are-not-a-list = {
      expr = (genProgram.declaration { } "x" "h").head;
      expectedError.msg = exactly "gen-program.declaration: relata is a string, expected a list of node identifiers (strings)";
    };
    test-program-refuses-a-record-relatum-at-the-declaration = {
      expr =
        genProgram.program
          [ "x" ]
          [
            {
              head = "h";
              relata = [ { name = "a"; } ];
            }
          ];
      expectedError.msg = exactly "gen-program.declaration: an entry of relata is a set, expected a node identifier (a string)";
    };
    test-unresolvedRelata-refuses-a-record-in-the-frozen-set = {
      expr =
        genProgram.unresolvedRelata
          [ { name = "a"; } ]
          [
            {
              head = "h";
              relata = [ "x" ];
            }
          ];
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

    # ── THE DOOR-CHECK BYTES (den-hoag-7gp66 P2) — R6's naming, pinned per door. `ci/tests/door-
    # checks.nix` pins that each door's violations are CATCHABLE at the application; a boolean
    # cannot see WHICH refusal fired, so WHICH is pinned here, one golden per door and failure mode.
    # `program`, `unresolvedRelata` and `ruleEdges` are positional (rule 4): their arity is
    # structural and they carry no field check, so no golden.
    test-body-missing-required-field-message = {
      expr = genProgram.body { name = "x"; };
      expectedError.msg = exactly "gen-program.body: required field 'clauses' is missing (required: 'name', 'clauses', 'declared') (in prelude.checkRequired)";
    };
    test-adjudicate-missing-required-field-message = {
      expr = genProgram.adjudicate {
        program = genProgram.program [ ] [ ];
        model = null;
      };
      expectedError.msg = exactly "gen-program.adjudicate: required field 'interpretation' is missing (required: 'program', 'model', 'interpretation') (in prelude.checkRequired)";
    };
    # den-hoag-ea3j4 landing gate Q4: `prior` is REQUIRED (arm (ii)) and was a native formal, so a
    # call without it aborted uncatchably. The door names it.
    test-model-missing-prior-message = {
      expr = genProgram.model {
        program = genProgram.program [ ] [ ];
        interpretation = [ ];
        complete = true;
      };
      expectedError.msg = exactly "gen-program.model: required field 'prior' is missing (required: 'program', 'interpretation', 'complete', 'prior') (in prelude.checkRequired)";
    };
    # The same gate's second abort: `mkModel` without `program` (ea3j4 P3).
    test-mkModel-missing-program-message = {
      expr = genProgram.mkModel {
        solved = null;
        adjudication = null;
        complete = true;
      };
      expectedError.msg = exactly "gen-program.mkModel: required field 'program' is missing (required: 'solved', 'program', 'adjudication', 'complete') (in prelude.checkRequired)";
    };
    test-mkModel-missing-adjudication-message = {
      expr = genProgram.mkModel {
        solved = null;
        program = null;
        complete = true;
      };
      expectedError.msg = exactly "gen-program.mkModel: required field 'adjudication' is missing (required: 'solved', 'program', 'adjudication', 'complete') (in prelude.checkRequired)";
    };
    test-declaration-unknown-option-message = {
      expr = genProgram.declaration { zzqran7f = 1; };
      expectedError.msg = exactly "gen-program.declaration: 'zzqran7f' is not an option of this door; the options are closed (accepted: 'pos', 'neg', 'label', 'when') (in prelude.checkOptions)";
    };
    # A declaration AS DATA — an entry of `program`'s list — is normalised by the same door's
    # record core: an unknown field and a missing `head` are refused by the door's name.
    test-declaration-record-unknown-field-message = {
      expr =
        genProgram.program
          [ ]
          [
            {
              head = "h";
              relata = [ ];
              zzqran7f = 1;
            }
          ];
      expectedError.msg = exactly "gen-program.declaration: 'zzqran7f' is not an option of this door; the options are closed (accepted: 'head', 'relata', 'pos', 'neg', 'label', 'when') (in prelude.checkOptions)";
    };
    test-declaration-record-missing-head-message = {
      expr = genProgram.program [ ] [ { relata = [ ]; } ];
      expectedError.msg = exactly "gen-program.declaration: required field 'head' is missing (required: 'head', 'relata') (in prelude.checkRequired)";
    };
    test-groundInstances-unknown-option-message = {
      expr = genProgram.groundInstances { zzqran7f = 1; };
      expectedError.msg = exactly "gen-program.groundInstances: 'zzqran7f' is not an option of this door; the options are closed (accepted: 'door', 'sources') (in prelude.checkOptions)";
    };

    # den-hoag-ea3j4 — the three refusals the multi-pass protocol names.
    test-withheld-negative-support-message = {
      expr =
        (
          (genProgram.model {
            prior = null;
            program =
              genProgram.program
                [ ]
                [
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
            interpretation = [ ];
            complete = false;
          }).resolve
            "a"
        ).included;
      expectedError.msg = exactly "gen-program: the membership 'a' is derived at this pass, but its support rests on negation and the relation is still growing (complete = false), so a later pass may still falsify it. van Antwerpen et al. 2018 §4.3 delays such a query rather than answering it; read `flag` and handle 'P'";
    };
    test-omitted-prior-declaration-message = {
      expr = genProgram.model {
        program =
          genProgram.program
            [ ]
            [
              {
                head = "z";
                relata = [ ];
              }
            ];
        interpretation = [ ];
        complete = true;
        prior = genProgram.model {
          prior = null;
          program =
            genProgram.program
              [ ]
              [
                {
                  head = "r";
                  relata = [ ];
                }
              ];
          interpretation = [ ];
          complete = false;
        };
      };
      expectedError.msg = exactly "gen-program.model: this pass's program drops 1 rule(s) of the prior pass, headed 'r' — every pass resubmits every earlier pass's declarations, because a prior pass's verdicts are not rules and a dropped declaration re-derives nothing it settled";
    };
    test-prior-not-a-record-message = {
      expr = genProgram.model {
        program = genProgram.program [ ] [ ];
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
        (genProgram.ruleEdges
          (modelOf true [
            {
              head = "s:a:b";
              relata = ab;
            }
          ])
          [
            {
              head = "r:a:b";
              relata = ab;
              label = "r";
            }
          ]
        ).reached;
      expectedError.msg = exactly "gen-program.ruleEdges: 'r:a:b' is labelled by a declaration that is not a rule of this model; the model was solved from other declarations, so it cannot answer for these";
    };
    # Keyed by head: a conflict is decidable from the declarations, so it refuses in `candidates`
    # with no model at all.
    test-rule-edges-refuses-conflicting-edges-for-one-head = {
      expr =
        (genProgram.ruleEdges (throw "no model was asked for") [
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
        ]).candidates;
      expectedError.msg = exactly "gen-program.ruleEdges: 'r:x' is labelled by declarations naming different edges; an edge is a property of the membership, so its declarations must agree on from, to and label";
    };
    test-rule-edges-refuses-a-labelled-declaration-not-relating-two = {
      expr =
        (genProgram.ruleEdges (throw "no model was asked for") [
          {
            head = "r:x";
            relata = [
              "a"
              "b"
              "c"
            ];
            label = "r";
          }
        ]).candidates;
      expectedError.msg = exactly "gen-program.ruleEdges: 'r:x' (3 relata) carries a label, but an edge relates exactly two relata, from and to";
    };
    test-declaration-refuses-a-label-that-is-not-a-string = {
      expr = (genProgram.declaration { label = 42; } ab "h").head;
      expectedError.msg = exactly "gen-program.declaration: the label is a int, expected an edge label (a string) or null";
    };
    # ── OPERAND DOORS (den-hoag-l3cwb): a wrong-shaped configuration operand is refused by name ──
    test-rule-edges-refuses-an-empty-model-operand = {
      expr = (genProgram.ruleEdges { } opLabelled).reached;
      expectedError.msg = exactly "gen-program.ruleEdges: the `model` operand (a gen-program result record): required field 'complete' is missing (required: 'complete', 'resolve', 'rules') (in prelude.checkRequired)";
    };
    test-rule-edges-refuses-a-non-attrset-model-operand = {
      expr = (genProgram.ruleEdges 5 opLabelled).reached;
      expectedError.msg = exactly "gen-program.ruleEdges: the `model` operand (a gen-program result record): the argument must be an attrset, not a int (required: 'complete', 'resolve', 'rules') (in prelude.checkRequired)";
    };
    test-rule-edges-refuses-a-model-whose-rules-is-not-a-set = {
      expr = (genProgram.ruleEdges (opModel // { rules = [ ]; }) opLabelled).reached;
      expectedError.msg = exactly "gen-program.ruleEdges: the `model` operand (a gen-program result record): field 'rules' must be an attrset, not a list";
    };
    test-adjudicate-refuses-an-empty-model-operand = {
      expr = (genProgram.adjudicate (opAdj // { model = { }; })).outcome;
      expectedError.msg = exactly "gen-program.adjudicate: the `model` operand (a gen-scope solved record): required field 'trueAtoms' is missing (required: 'trueAtoms', 'undefinedAtoms') (in prelude.checkRequired)";
    };
    test-adjudicate-refuses-a-model-whose-undefined-atoms-is-not-a-list = {
      expr =
        (genProgram.adjudicate (
          opAdj
          // {
            model = opSolved // {
              undefinedAtoms = "s";
            };
          }
        )).outcome;
      expectedError.msg = exactly "gen-program.adjudicate: the `model` operand (a gen-scope solved record): field 'undefinedAtoms' must be a list of strings, not a string";
    };
    test-adjudicate-refuses-an-empty-program-operand = {
      expr = (genProgram.adjudicate (opAdj // { program = { }; })).outcome;
      expectedError.msg = exactly "gen-program.adjudicate: the `program` operand (a gen-scope program value, as `program` returns): required field 'atoms' is missing (required: 'atoms', 'bodyArity', 'dependency', 'rules', 'signs', 'unaryBodies') (in prelude.checkRequired)";
    };
    test-adjudicate-refuses-a-non-list-interpretation-operand = {
      expr = (genProgram.adjudicate (opAdj // { interpretation = null; })).outcome;
      expectedError.msg = exactly "gen-program.adjudicate: the `interpretation` operand must be a list, not a null";
    };
    test-mk-model-refuses-an-empty-solved-operand = {
      expr = (genProgram.mkModel (opMk // { solved = { }; })).condensationDepth;
      expectedError.msg = exactly "gen-program.mkModel: the `solved` operand (a gen-scope solved record): required field 'condensationDepth' is missing (required: 'condensationDepth', 'converged', 'falseAtoms', 'provenance', 'trueAtoms', 'undefinedAtoms', 'verdict') (in prelude.checkRequired)";
    };
    test-mk-model-refuses-a-solved-without-a-verdict = {
      expr =
        (genProgram.mkModel (opMk // { solved = removeAttrs opSolved [ "verdict" ]; })).condensationDepth;
      expectedError.msg = exactly "gen-program.mkModel: the `solved` operand (a gen-scope solved record): required field 'verdict' is missing (required: 'condensationDepth', 'converged', 'falseAtoms', 'provenance', 'trueAtoms', 'undefinedAtoms', 'verdict') (in prelude.checkRequired)";
    };
    test-mk-model-refuses-an-empty-program-operand = {
      expr = (genProgram.mkModel (opMk // { program = { }; })).condensationDepth;
      expectedError.msg = exactly "gen-program.mkModel: the `program` operand (a gen-scope program value, as `program` returns): required field 'atoms' is missing (required: 'atoms', 'bodyArity', 'dependency', 'rules', 'signs', 'unaryBodies') (in prelude.checkRequired)";
    };
    test-mk-model-refuses-a-non-set-adjudication-operand = {
      expr = (genProgram.mkModel (opMk // { adjudication = null; })).condensationDepth;
      expectedError.msg = exactly "gen-program.mkModel: the `adjudication` operand must be an attrset, not a null";
    };
    test-mk-model-refuses-a-non-boolean-complete-operand = {
      expr = (genProgram.mkModel (opMk // { complete = "s"; })).condensationDepth;
      expectedError.msg = exactly "gen-program.mkModel: the `complete` operand must be a boolean, not a string";
    };
    test-model-refuses-an-empty-program-operand = {
      expr = (genProgram.model (opModelArgs // { program = { }; })).complete;
      expectedError.msg = exactly "gen-program.model: the `program` operand (a gen-scope program value, as `program` returns): required field 'atoms' is missing (required: 'atoms', 'bodyArity', 'dependency', 'rules', 'signs', 'unaryBodies') (in prelude.checkRequired)";
    };
    test-model-refuses-a-non-list-interpretation-operand = {
      expr = (genProgram.model (opModelArgs // { interpretation = "s"; })).complete;
      expectedError.msg = exactly "gen-program.model: the `interpretation` operand must be a list, not a string";
    };
    test-model-refuses-a-non-boolean-complete-operand = {
      expr = (genProgram.model (opModelArgs // { complete = null; })).complete;
      expectedError.msg = exactly "gen-program.model: the `complete` operand must be a boolean, not a null";
    };
    test-codomain-breaches-refuses-an-empty-contract-operand = {
      expr = genProgram.codomainBreaches { } [ ];
      expectedError.msg = exactly "gen-program.codomainBreaches: the `contract` operand (a codomain `{ emits; binds; suppresses; }`): required field 'binds' is missing (required: 'binds', 'emits', 'suppresses') (in prelude.checkRequired)";
    };
    test-codomain-breaches-refuses-a-binds-that-is-not-a-list-or-null = {
      expr = genProgram.codomainBreaches {
        emits = [ ];
        binds = "s";
        suppresses = [ ];
      } [ ];
      expectedError.msg = exactly "gen-program.codomainBreaches: the `contract` operand (a codomain `{ emits; binds; suppresses; }`): field 'binds' must be a list or null, not a string";
    };
    # ── the element form of an atom list (C-C): a non-string atom aborts the evaluator uncatchably, so it is refused here ──
    test-adjudicate-refuses-a-true-atom-that-is-not-a-string = {
      expr =
        (genProgram.adjudicate (
          opAdj
          // {
            model = opSolved // {
              trueAtoms = [ 5 ];
            };
          }
        )).outcome;
      expectedError.msg = exactly "gen-program.adjudicate: the `model` operand (a gen-scope solved record): field 'trueAtoms' must be a list of strings, not a list holding a int";
    };
    test-adjudicate-refuses-an-undefined-atom-that-is-not-a-string = {
      expr =
        (genProgram.adjudicate (
          opAdj
          // {
            model = opSolved // {
              undefinedAtoms = [ 5 ];
            };
          }
        )).outcome;
      expectedError.msg = exactly "gen-program.adjudicate: the `model` operand (a gen-scope solved record): field 'undefinedAtoms' must be a list of strings, not a list holding a int";
    };
    test-mk-model-refuses-a-true-atom-that-is-not-a-string-while-growing = {
      expr =
        (genProgram.mkModel (
          opMk
          // {
            complete = false;
            solved = opSolved // {
              trueAtoms = [ 5 ];
            };
          }
        )).condensationDepth;
      expectedError.msg = exactly "gen-program.mkModel: the `solved` operand (a gen-scope solved record): field 'trueAtoms' must be a list of strings, not a list holding a int";
    };
    test-mk-model-refuses-a-false-atom-that-is-not-a-string-when-complete = {
      expr =
        (genProgram.mkModel (
          opMk
          // {
            solved = opSolved // {
              falseAtoms = [ 5 ];
            };
          }
        )).condensationDepth;
      expectedError.msg = exactly "gen-program.mkModel: the `solved` operand (a gen-scope solved record): field 'falseAtoms' must be a list of strings, not a list holding a int";
    };
  };
}
