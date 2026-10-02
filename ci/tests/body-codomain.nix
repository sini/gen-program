# ORACLES O2 (the derivability checker's shape) + O5 (order/multiplicity invariance).
#
# ★ THE ARMED CELL IS THE POINT OF O2. `deriveCodomain`'s signature has no context parameter —
# the checker is its own by-construction proof that no derived fact depends on the firing
# context. Here that is ARMED rather than asserted. On terms (den-hoag-lwbb1 unit 3) a slot is data
# the walk reads, so the arming is in RESOLUTION: every term slot of the armed body refuses when
# resolved at any context, and its door clause's door detonates when called. The body derives its
# codomain clean; the control beside it resolves the same body and refuses, so the arming is live.
# There is no sentinel firing anywhere in the derivation path (defect C has no expression).
#
# O5 is ADR-0022's alignment as a mechanical check: the folds are unions, so the derived codomain
# is byte-identical under permutation of the clause list and under an `over` yielding nothing,
# one item, or many — `over` is never read, which is why it may be any list-valued term.
{
  genProgram,
  T,
  ...
}:
let
  t = T.term;
  # Every read of `env` projects a path the context never has, so each one refuses on resolution.
  detonating = t.readCtx "env" [ "never-present" ];
  armedDoor =
    (T.refId {
      declared = {
        site = "armed";
        reads = [ "env" ];
      };
    }).right;
  armed = genProgram.body {
    name = "armed";
    declared = [ "env" ];
    clauses = [
      (genProgram.forEach {
        over = detonating;
        emit = [
          {
            ctor = "member";
            kind = "k";
            when = t.has "env";
            payload = {
              a = detonating;
            };
          }
        ];
      })
      (genProgram.emit {
        ctor = "edge";
        when = t.has "env";
        target = detonating;
      })
      {
        when = t.has "env";
        body = t.ref armedDoor;
        emits = [ "d" ];
        binds = [ ];
        suppresses = [ ];
      }
    ];
  };

  clauseA = genProgram.emit {
    ctor = "member";
    kind = "host";
    when = t.has "host";
    payload = {
      host = t.readCtx "host" [ ];
    };
  };
  clauseB = genProgram.emit {
    ctor = "suppress";
    target = "user-to-host";
  };
  clauseC = genProgram.emit {
    ctor = "deliver";
    payload = {
      fromClass = t.lit "a";
      intoClass = t.lit "b";
      path = t.lit [ ];
    };
  };

  bodyOf =
    clauses:
    genProgram.body {
      name = "o5";
      declared = null;
      inherit clauses;
    };

  multiBody =
    over:
    genProgram.body {
      name = "o5-multiplicity";
      declared = null;
      clauses = [
        (genProgram.forEach {
          inherit over;
          emit = [
            {
              ctor = "member";
              kind = "environment";
              payload = {
                environment = t.readCtx "item" [ ];
              };
            }
          ];
        })
      ];
    };
in
{
  flake.tests.bodyCodomain = {
    # ── O2: THE CHECKER'S SHAPE ──
    test-derive-codomain-takes-a-single-body-and-no-context = {
      expr = builtins.functionArgs genProgram.deriveCodomain;
      expected = { };
    };
    test-the-armed-body-derives-clean-no-free-slot-is-ever-forced = {
      expr = genProgram.deriveCodomain armed;
      expected = {
        emits = [
          "d"
          "edge"
          "k"
        ];
        binds = [ "a" ];
        suppresses = [ ];
      };
    };

    # The arming is live: resolving the same body at a context refuses — the forEach's `over` reads
    # a path the context lacks — so a derivation that resolved anything would have met it. (The
    # door here answers a refusal rather than throwing: resolving DOES reach it.)
    test-control-the-armed-body-refuses-when-resolved = {
      expr =
        (genProgram.groundInstances {
          body = armed;
          context.env = { };
          door = _: {
            left = {
              code = "armed-door";
              witness = { };
            };
          };
        }).code;
      expected = "policy-body/projection-path-missing";
    };

    # ── O5: PERMUTATION ──
    test-o5-the-codomain-is-invariant-under-clause-permutation = {
      expr = genProgram.deriveCodomain (bodyOf [
        clauseA
        clauseB
        clauseC
      ]);
      expected = genProgram.deriveCodomain (bodyOf [
        clauseC
        clauseA
        clauseB
      ]);
    };

    # ── O5: MULTIPLICITY ──
    # Three bodies identical except in what `over` yields: nothing, one item, many. The fold
    # never reads `over`, so all three derive byte-identically.
    test-o5-the-codomain-is-invariant-under-over-yielding-none-one-or-many = {
      expr = map (over: genProgram.deriveCodomain (multiBody over)) [
        (t.lit [ ])
        (t.lit [ 1 ])
        (t.lit [
          1
          2
          3
        ])
      ];
      expected =
        let
          one = {
            emits = [ "environment" ];
            binds = [ "environment" ];
            suppresses = [ ];
          };
        in
        [
          one
          one
          one
        ];
    };

    # ── THE EQUALITY DISCRIMINATES ──
    # Two bodies differing in a skeleton derive DIFFERENT codomains — the invariance cells above
    # are equalities, and an equality that cannot fail measures nothing.
    test-control-a-body-differing-in-a-skeleton-derives-differently = {
      expr =
        genProgram.deriveCodomain (bodyOf [
          clauseA
          clauseB
        ]) == genProgram.deriveCodomain (bodyOf [ clauseA ]);
      expected = false;
    };
  };
}
