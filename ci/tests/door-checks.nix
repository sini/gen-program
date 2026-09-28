# THE CLOSED-DOOR CHECKS (den-hoag-7gp66 P1) — every published door catches its own violations.
#
# A native closed formal (`{ declarations, frozen }:` and its siblings) aborts UNCATCHABLY on a
# missing argument — not even `builtins.tryEval` sees it, which is ADR-0025 item 1's named defect.
# `unresolvedRelata`, `program`, `body` and `adjudicate` now take a bare positional formal and
# apply gen-prelude's shared `checkRequired` (0ac7b66) instead, so the same violation is NAMED and
# CATCHABLE.
#
# ★ THE FIRST FOUR ARE RECORD-CLASS DOORS: every field is required, so `checkRequired` runs alone
# and R5's stated price applies uniformly — the door is OPEN, an extra field is admitted, never
# refused.
#
# ★★ `declaration`, `model`, `mkModel` and `escape` ARE NATIVE-ELLIPSIS CLASS DOORS instead
# (den-hoag-7gp66 P1, owner-ruled arm (C)): each is read by `builtins.functionArgs` from an ORACLE
# this repository already ships (O4/O6, `identifier-doors.nix`, `relation.nix`, `staging.nix`,
# `surface.nix`, `adjudication.nix`, `body-escape.nix`), and den-hoag-bkdkg rules that a WRAPPER
# around the door is detectable — it erases the formals a caller reads. The ruled resolution is not
# a wrapper: the pattern stays native (so a MISSING required field still aborts the evaluator's own
# uncatchable way, undisturbed and untested here — that is O6's requirement, not this suite's
# subject) and gains an `...` formal, and the body runs `prelude.checkOptions` over the raw `args`
# so an UNKNOWN field is what moves — named and caught instead of aborting the identical uncatchable
# way a missing one still does. `builtins.functionArgs` reads the same named formals either way,
# which is what keeps the nine oracle assertions above unmoved.
#
# WHICH refusal fired is a claim about the message and `tryEval` yields only `success`; the byte
# goldens naming each door (R6) live in `ci/tests-error.nix`'s `flake.testsError`.
{
  genProgram,
  scope,
  ...
}:
let
  inherit (genProgram)
    unresolvedRelata
    program
    body
    adjudicate
    declaration
    model
    mkModel
    escape
    ;

  # `success == false` pins catchability, not the message — the byte goldens are the message's own
  # test. Forced with `deepSeq null` so a lazily-returned attrset's unread check still runs.
  refusesCatchably = e: !(builtins.tryEval (builtins.deepSeq e null)).success;
  answers = e: (builtins.tryEval (builtins.deepSeq e null)).success;

  # ★ `firesAtApplication` (den-hoag-7gp66 P1 strictness sweep) is `refusesCatchably`'s WHNF-only
  # twin: a bare `builtins.seq`, matching what merely APPLYING a door forces, with no later field
  # read. This is the distinct defect the sweep measured on `body`: `refusesCatchably` above passed
  # for a missing required field there even before the strictness fix, because `deepSeq` reached the
  # refusal's `culprit` field and re-triggered a check that a bare `seq` on the door's own return
  # never touched. `answers`'s WHNF twin is not needed — an admitted RECORD-class extra field is a
  # data question (does it construct), not a strictness one.
  firesAtApplication = e: !(builtins.tryEval (builtins.seq e null)).success;

  validProgram = program {
    declarations = [ ];
    frozen = [ ];
  };
  validInterpretation = [ ];
  validSolved = scope.solve validInterpretation validProgram;
in
{
  flake.tests.door-checks = {
    # ★ LIVE CONTROL FOR THE WHOLE SUITE, first: `tryEval` catches an ORDINARY throw, and a
    # non-throwing value answers. Without this, every `refusesCatchably`/`answers` cell below is
    # equally consistent with a broken helper that reads `false` no matter what it is handed.
    test-control-tryeval-catches-an-ordinary-throw = {
      expr = refusesCatchably (throw "control probe, not this suite's subject");
      expected = true;
    };
    test-control-tryeval-answers-a-non-throwing-value = {
      expr = answers 1;
      expected = true;
    };

    # ★★ LIVE CONTROL FOR `firesAtApplication`, BOTH ARMS: a throw hidden behind an unread field
    # reads `false` — the predicate does not mistake a merely-`deepSeq`-reachable check for a
    # WHNF-strict one — and a bare throw reads `true`. This is `body`'s own pre-fix shape (a throw
    # reachable only through a field nothing here forces) in miniature, so a `false` on the door
    # cells below is attributable to the SAME mechanism this control exercises, not a fluke.
    test-control-firesAtApplication-is-false-for-a-throw-behind-an-unread-field = {
      expr = firesAtApplication { culprit = throw "control probe, not this suite's subject"; };
      expected = false;
    };
    test-control-firesAtApplication-is-true-for-an-ordinary-throw = {
      expr = firesAtApplication (throw "control probe, not this suite's subject");
      expected = true;
    };

    # unresolvedRelata — RECORD class.
    test-unresolvedRelata-missing-required-field-refused-catchably = {
      expr = refusesCatchably (unresolvedRelata {
        declarations = [ ];
      });
      expected = true;
    };
    test-unresolvedRelata-extra-field-on-a-record-is-admitted = {
      expr = answers (unresolvedRelata {
        declarations = [ ];
        frozen = [ ];
        zzqran7f = 1;
      });
      expected = true;
    };
    test-unresolvedRelata-valid-call-is-unchanged = {
      expr = unresolvedRelata {
        declarations = [ ];
        frozen = [ ];
      };
      expected = [ ];
    };

    # program — RECORD class.
    test-program-missing-required-field-refused-catchably = {
      expr = refusesCatchably (program {
        declarations = [ ];
      });
      expected = true;
    };
    test-program-extra-field-on-a-record-is-admitted = {
      expr = answers (program {
        declarations = [ ];
        frozen = [ ];
        zzqran7f = 1;
      });
      expected = true;
    };

    # body — RECORD class.
    test-body-missing-required-field-refused-catchably = {
      expr = refusesCatchably (body {
        name = "x";
      });
      expected = true;
    };
    # ★ den-hoag-7gp66 P1 strictness fix, 2026-09-27: RED on the pre-fix door — `refusesCatchably`
    # above already passed on the unfixed door, because `deepSeq` reached the returned refusal's
    # `culprit` field and re-triggered `checkRequired`'s cached throw; a bare `builtins.seq` on the
    # door's own return did not, so the check ran only behind a field read nothing at application
    # forces. `builtins.seq checked (…)` at the return is what makes this cell strict.
    test-body-missing-required-field-fires-at-application = {
      expr = firesAtApplication (body {
        name = "x";
      });
      expected = true;
    };
    test-body-extra-field-on-a-record-is-admitted = {
      expr = answers (body {
        name = "x";
        clauses = [ ];
        zzqran7f = 1;
      });
      expected = true;
    };
    test-body-valid-call-is-unchanged = {
      expr = body {
        name = "x";
        clauses = [ ];
      };
      expected = {
        refused = false;
        opaque = false;
        name = "x";
        clauses = [ ];
      };
    };

    # adjudicate — RECORD class.
    test-adjudicate-missing-required-field-refused-catchably = {
      expr = refusesCatchably (adjudicate {
        program = validProgram;
        model = validSolved;
      });
      expected = true;
    };
    test-adjudicate-extra-field-on-a-record-is-admitted = {
      expr = answers (adjudicate {
        program = validProgram;
        model = validSolved;
        interpretation = validInterpretation;
        zzqran7f = 1;
      });
      expected = true;
    };
    test-adjudicate-valid-call-is-unchanged = {
      expr =
        (adjudicate {
          program = validProgram;
          model = validSolved;
          interpretation = validInterpretation;
        }).outcome;
      expected = "admitted";
    };

    # declaration/model/mkModel/escape — NATIVE-ELLIPSIS class (arm (C)). A MISSING required field
    # is not tested here: it is still the evaluator's own uncatchable abort, untouched by this
    # landing (O6's requirement) — `ci/tests/staging.nix` and its siblings already pin that the
    # formal stays required. What is new is that an UNKNOWN field, which used to abort the
    # identical uncatchable way, is now named and caught by `prelude.checkOptions`.
    test-declaration-unknown-field-refused-catchably = {
      expr = refusesCatchably (declaration {
        head = "h";
        relata = [ ];
        zzqran7f = 1;
      });
      expected = true;
    };
    test-model-unknown-field-refused-catchably = {
      expr = refusesCatchably (model {
        program = validProgram;
        interpretation = validInterpretation;
        complete = true;
        zzqran7f = 1;
      });
      expected = true;
    };
    test-mkModel-unknown-field-refused-catchably = {
      expr = refusesCatchably (mkModel {
        solved = validSolved;
        adjudication = null;
        complete = true;
        zzqran7f = 1;
      });
      expected = true;
    };
    test-escape-unknown-field-refused-catchably = {
      expr = refusesCatchably (escape {
        name = "x";
        fn = _: { };
        emits = [ ];
        binds = [ ];
        suppresses = [ ];
        zzqran7f = 1;
      });
      expected = true;
    };

    # ★ den-hoag-7gp66 P1 strictness sweep, 2026-09-27: the four cells above already used
    # `refusesCatchably` (`deepSeq`); these re-assert the identical calls with `firesAtApplication`
    # (a bare `seq`) to pin that each door's `checkOptions` runs unconditionally at the top of its
    # own body — `builtins.seq (checkOptions …) (…)` — rather than only behind a later field read,
    # which is the defect class `body` had (see above) and these four doors never did.
    test-declaration-unknown-field-fires-at-application = {
      expr = firesAtApplication (declaration {
        head = "h";
        relata = [ ];
        zzqran7f = 1;
      });
      expected = true;
    };
    test-model-unknown-field-fires-at-application = {
      expr = firesAtApplication (model {
        program = validProgram;
        interpretation = validInterpretation;
        complete = true;
        zzqran7f = 1;
      });
      expected = true;
    };
    test-mkModel-unknown-field-fires-at-application = {
      expr = firesAtApplication (mkModel {
        solved = validSolved;
        adjudication = null;
        complete = true;
        zzqran7f = 1;
      });
      expected = true;
    };
    test-escape-unknown-field-fires-at-application = {
      expr = firesAtApplication (escape {
        name = "x";
        fn = _: { };
        emits = [ ];
        binds = [ ];
        suppresses = [ ];
        zzqran7f = 1;
      });
      expected = true;
    };
  };
}
