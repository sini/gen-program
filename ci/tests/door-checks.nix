# THE DOOR CHECKS (den-hoag-7gp66 P2 — `prelude.door`, R7 argument structure / R5 field closure) —
# every published step of gen-program that takes a RECORD catches its own violations, at its own
# application, catchably.
#
# After P2 a door step is one of two kinds (spec §p2.3.1):
#   · an OPTIONS step — one closed set, first in the call: `declaration { pos?; neg?; label?;
#     promote?; when?; } relata head` and `groundInstances { door?; sources?; } context body`;
#   · a KEYED RECORD — open (R5), every field required, kept as one record because its fields are
#     two or more configuration operands with no natural order (the keyed-record ruling,
#     2026-09-28): `model`, `mkModel`, `adjudicate`, `body`.
# `program frozen declarations`, `unresolvedRelata frozen declarations` and `ruleEdges model
# declarations` are positional (rule 4): their arity is structural and they carry no row. No record
# step sits behind an options step here, so no door carries `optionsStep` (G10 has no row).
#
# WHICH refusal fired is a claim about the message and `tryEval` yields only `success`; the byte
# goldens naming each door (R6) live in `ci/tests-error.nix`'s `flake.testsError`.
{
  genProgram,
  scope,
  prelude,
  ...
}:
let
  # `firesAtApplication` forces the door's application to WHNF only — never `deepSeq` — so a check
  # that ran only behind a later field read reads `false` (spec §p2.5, premise 5).
  firesAtApplication = e: !(builtins.tryEval (builtins.seq e null)).success;
  answers = e: (builtins.tryEval (builtins.deepSeq e null)).success;

  validProgram = genProgram.program [ ] [ ];
  validSolved = scope.solve [ ] validProgram;
  adjudication = genProgram.adjudicate {
    program = validProgram;
    model = validSolved;
    interpretation = [ ];
  };

  # The options rows: the door, its options, and one non-default option whose value the door's
  # own result carries (G3). `apply` supplies the operands after the options step.
  optionsRows = {
    declaration = {
      optional = [
        "pos"
        "neg"
        "label"
        "promote"
        "when"
      ];
      apply = f: f [ "x" ] "h";
      observe = r: r.neg;
      opt = {
        neg = [ "q" ];
      };
    };
    groundInstances = {
      optional = [
        "door"
        "sources"
      ];
      # A body with one door clause: the `door` option is what resolves it, so the result reads
      # the option (G3); with `{ }` the door clause resolves to nothing.
      apply =
        f:
        f { } (
          genProgram.body {
            name = "g3";
            declared = null;
            clauses = [ ];
          }
        );
      observe = r: r;
      opt = null;
    };
  };

  # The keyed-record rows: the door, its required fields, and a `good` record that answers (each
  # row's live control, so a refusal below is the check firing, not a broken fixture).
  recordRows = {
    model = {
      required = [
        "program"
        "interpretation"
        "complete"
        "prior"
      ];
      good = {
        program = validProgram;
        interpretation = [ ];
        complete = true;
        prior = null;
      };
    };
    mkModel = {
      required = [
        "solved"
        "program"
        "adjudication"
        "complete"
      ];
      good = {
        solved = validSolved;
        program = validProgram;
        inherit adjudication;
        complete = true;
      };
    };
    adjudicate = {
      required = [
        "program"
        "model"
        "interpretation"
      ];
      good = {
        program = validProgram;
        model = validSolved;
        interpretation = [ ];
      };
    };
    body = {
      required = [
        "name"
        "clauses"
        "declared"
      ];
      good = {
        name = "x";
        clauses = [ ];
        declared = null;
      };
    };
  };

  # A field name no door declares, generated per evaluation from the door names themselves, so it is
  # never a name any contract below lists.
  stranger = "not-a-field-of-" + builtins.concatStringsSep "-" (builtins.attrNames recordRows);

  perOptions = f: builtins.mapAttrs f optionsRows;
  perRecord = f: builtins.mapAttrs f recordRows;
  allTrue = rows: builtins.all (x: x) (builtins.attrValues rows);

  # Every published value that is a door (a functor carrying `__contract`).
  surfaceDoors = builtins.attrNames (
    prelude.filterAttrs (_: v: builtins.isAttrs v && v ? __functor && v ? __contract) genProgram
  );
in
{
  flake.tests.door-checks = {
    # ── LIVE CONTROLS, first: the predicates are not dead ──
    test-control-firesAtApplication-is-true-for-an-ordinary-throw = {
      expr = firesAtApplication (throw "control probe, not this suite's subject");
      expected = true;
    };
    test-control-firesAtApplication-is-false-for-a-throw-behind-an-unread-field = {
      expr = firesAtApplication { culprit = throw "control probe, not this suite's subject"; };
      expected = false;
    };

    # ── THE TABLE IS THE SURFACE ──
    # Every published door has a row and every row is a published door, so a door added without a
    # row — or a row whose door reverted to a lambda — reds here.
    test-the-door-table-equals-the-surface-doors = {
      expr = surfaceDoors;
      expected = builtins.sort (a: b: a < b) (
        builtins.attrNames optionsRows ++ builtins.attrNames recordRows
      );
    };
    test-the-positional-entries-are-plain-lambdas = {
      expr = map (n: builtins.isFunction genProgram.${n}) [
        "program"
        "unresolvedRelata"
        "ruleEdges"
      ];
      expected = [
        true
        true
        true
      ];
    };

    # ── OPTIONS STEPS ──
    # G1/G4: an unknown option is refused at `f opts`'s WHNF, before any operand.
    test-an-unknown-option-is-refused-at-the-options-application = {
      expr = perOptions (n: _: firesAtApplication (genProgram.${n} { ${stranger} = 1; }));
      expected = perOptions (_: _: true);
    };
    test-a-non-set-options-argument-is-refused-at-the-application = {
      expr = perOptions (n: _: firesAtApplication (genProgram.${n} 1));
      expected = perOptions (_: _: true);
    };
    # The live control: `{ }` forms the door and the operands answer.
    test-control-the-empty-options-answer = {
      expr = perOptions (n: r: answers (r.apply (genProgram.${n} { })));
      expected = perOptions (_: _: true);
    };
    # D3: the published contract and the functor-aware reader agree with the row.
    test-each-options-door-publishes-its-contract = {
      expr = perOptions (
        n: _: {
          inherit (genProgram.${n}.__contract) optional open required;
          args = prelude.functionArgs genProgram.${n};
        }
      );
      expected = perOptions (
        _: r: {
          inherit (r) optional;
          open = false;
          required = [ ];
          args = builtins.listToAttrs (map (f: prelude.nameValuePair f true) r.optional);
        }
      );
    };
    # G3: a non-default option reaches the result, and agrees with the full call. `groundInstances`
    # has no option whose value its own result carries over a closed body — `door` and `sources` are
    # read only by a door clause's firing — so G4 alone stands for it, named here.
    test-a-non-default-option-reaches-the-result = {
      expr =
        let
          r = optionsRows.declaration;
          f1 = genProgram.declaration r.opt;
        in
        {
          agree = r.observe (r.apply f1) == r.observe (genProgram.declaration r.opt [ "x" ] "h");
          differ = r.observe (r.apply f1) != r.observe (r.apply (genProgram.declaration { }));
        };
      expected = {
        agree = true;
        differ = true;
      };
    };
    test-g3-names-the-door-whose-result-carries-no-option = {
      expr = builtins.attrNames (prelude.filterAttrs (_: r: r.opt == null) optionsRows);
      expected = [ "groundInstances" ];
    };

    # ── KEYED RECORDS ──
    # The live control: each row's `good` record answers through its door.
    test-control-each-good-record-answers = {
      expr = perRecord (n: r: answers (genProgram.${n} r.good));
      expected = perRecord (_: _: true);
    };
    # D2: EVERY required field, dropped alone, is refused at the application — including the two the
    # ea3j4 landing gate named (`model` without `prior`, `mkModel` without `program`).
    test-each-missing-field-is-refused-at-the-application = {
      expr = perRecord (
        n: r:
        allTrue (
          prelude.genAttrs r.required (f: firesAtApplication (genProgram.${n} (removeAttrs r.good [ f ])))
        )
      );
      expected = perRecord (_: _: true);
    };
    test-a-non-set-record-is-refused-at-the-application = {
      expr = perRecord (n: _: firesAtApplication (genProgram.${n} 1));
      expected = perRecord (_: _: true);
    };
    # G2: R5's price — an extra field is admitted, and the answer is unchanged.
    test-an-extra-field-is-admitted = {
      expr = perRecord (n: r: answers (genProgram.${n} (r.good // { ${stranger} = 1; })));
      expected = perRecord (_: _: true);
    };
    # D3.
    test-each-record-door-publishes-its-contract = {
      expr = perRecord (
        n: _: {
          inherit (genProgram.${n}.__contract) required optional open;
          args = prelude.functionArgs genProgram.${n};
        }
      );
      expected = perRecord (
        _: r: {
          inherit (r) required;
          optional = [ ];
          open = true;
          args = builtins.listToAttrs (map (f: prelude.nameValuePair f false) r.required);
        }
      );
    };

    # ── A DECLARATION AS DATA ──
    # An entry of `program`'s list is normalised by the declaration door's record core: an unknown
    # field and a missing `head` or `relata` are refused catchably, where the native formal aborted.
    test-a-declaration-record-with-an-unknown-field-is-refused = {
      expr = firesAtApplication (
        genProgram.program
          [ ]
          [
            {
              head = "h";
              relata = [ ];
              ${stranger} = 1;
            }
          ]
      );
      expected = true;
    };
    test-a-declaration-record-missing-a-required-field-is-refused = {
      expr = map (r: firesAtApplication (genProgram.program [ ] [ r ])) [
        { relata = [ ]; }
        { head = "h"; }
      ];
      expected = [
        true
        true
      ];
    };
    test-control-a-whole-declaration-record-answers = {
      expr = answers (
        genProgram.program
          [ ]
          [
            {
              head = "h";
              relata = [ ];
            }
          ]
      );
      expected = true;
    };
  };
}
