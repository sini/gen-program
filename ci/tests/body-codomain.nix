# ORACLES O2 (the derivability checker's shape) + O5 (order/multiplicity invariance).
#
# ★ THE ARMED CELL IS THE POINT OF O2. `deriveCodomain`'s signature has no context parameter —
# the checker is its own by-construction proof that no derived fact depends on the firing
# context. Here that is ARMED rather than asserted: a body whose every free slot detonates —
# `over` a bare throw, `when` and every payload value throwing on application, a free target a
# bare throw — derives its codomain clean. If the derivation ever forced a free slot, this cell
# reds; there is no sentinel firing anywhere in the derivation path (defect C has no expression).
#
# O5 is ADR-0022's alignment as a mechanical check: the folds are unions, so the derived codomain
# is byte-identical under permutation of the clause list and under an `over` yielding nothing,
# one item, or many — `over` is never read, which is why it may be fully free.
{
  genProgram,
  prelude,
  ...
}:
let
  armed = genProgram.body {
    name = "armed";
    clauses = [
      (genProgram.forEach {
        over = throw "over must never be forced by the derivation";
        emit = [
          {
            ctor = "member";
            kind = "k";
            when = _: throw "when must never be applied by the derivation";
            payload = {
              a = _: throw "a payload value must never be applied by the derivation";
            };
          }
        ];
      })
      (genProgram.emit {
        ctor = "edge";
        target = throw "a free target must never be forced by the derivation";
      })
    ];
  };

  clauseA = genProgram.emit {
    ctor = "member";
    kind = "host";
    payload = {
      host = s: s.host;
    };
  };
  clauseB = genProgram.emit {
    ctor = "suppress";
    target = "user-to-host";
  };
  clauseC = genProgram.emit {
    ctor = "deliver";
    payload = {
      fromClass = _: "a";
      intoClass = _: "b";
      path = _: [ ];
    };
  };

  bodyOf =
    clauses:
    genProgram.body {
      name = "o5";
      inherit clauses;
    };

  multiBody =
    over:
    genProgram.body {
      name = "o5-multiplicity";
      clauses = [
        (genProgram.forEach {
          inherit over;
          emit = [
            {
              ctor = "member";
              kind = "environment";
              payload = {
                environment = { item, ... }: item;
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
          "edge"
          "k"
        ];
        binds = [ "a" ];
        suppresses = [ ];
      };
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
        (_: [ ])
        (_: [ 1 ])
        (_: [
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
