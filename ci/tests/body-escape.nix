# ORACLE O4 — THE CODOMAIN CONTRACT IS CONTRACTED AT EVERY FIRING; THE ESCAPE THAT CARRIED IT IS
# RETIRED.
#
# The per-firing check is the whole difference between a declared codomain and an inert one
# (ADR-0008: the licence is the contract, and an uncontracted projection rots into vacuity). It
# was the declared escape's firing path; the escape is retired (den-hoag-lwbb1 unit 3, U3r) and the
# check is `codomainBreaches`, which the gen-rules door applies at every firing. All three
# directions are seeded — an emission outside `emits`, a member-binding key outside `binds`, an
# exclusion outside `suppresses` — and the green control is the same firing under its honest
# contract, clean in the same run.
#
# ★ THE RETIREMENT IS ASSERTED AS A CONSTRUCTION: the retired constructor mints no escape record,
# `admit` refuses one by name rather than checking its contract, and a bare lambda is refused with
# the signpost to the door — no silent entry, and no silent deletion.
{
  genProgram,
  prelude,
  ...
}:
let
  ctx = {
    host = {
      name = "web1";
    };
  };
  breaches = contract: fn: genProgram.codomainBreaches contract (fn ctx);
  code = r: if builtins.isAttrs r && (r.refused or false) then r.code else "admitted";

  # Fires a member-binding of kind "host" carrying `host` and `accessGroups`.
  bindsFn = c: [
    {
      ctor = "member";
      kind = "host";
      payload = {
        host = c.host;
        accessGroups = [ "admins" ];
      };
    }
  ];
in
{
  flake.tests.bodyEscape = {
    # ── THE THREE SEEDED BREACHES, EACH NAMED WITH ITS FIELD AND DELTA ──
    test-o4-an-emission-outside-emits-is-refused-at-the-firing = {
      expr =
        breaches
          {
            emits = [ "edge" ];
            binds = [ ];
            suppresses = [ ];
          }
          (_: [
            {
              ctor = "member";
              kind = "host";
              payload = { };
            }
          ]);
      expected = [
        {
          field = "emits";
          delta = "host";
        }
      ];
    };
    test-o4-a-member-binding-key-outside-binds-is-refused-at-the-firing = {
      expr = breaches {
        emits = [ "host" ];
        binds = [ "host" ];
        suppresses = [ ];
      } bindsFn;
      expected = [
        {
          field = "binds";
          delta = "accessGroups";
        }
      ];
    };
    test-o4-an-exclusion-outside-suppresses-is-refused-at-the-firing = {
      expr =
        breaches
          {
            emits = [ ];
            binds = [ ];
            suppresses = [ ];
          }
          (_: [
            {
              ctor = "suppress";
              target = "user-to-host";
            }
          ]);
      expected = [
        {
          field = "suppresses";
          delta = "user-to-host";
        }
      ];
    };

    # ── THE GREEN CONTROL: THE HONEST CONTRACT FIRES CLEAN, SAME BODY, SAME RUN ──
    test-control-o4-the-same-body-under-its-honest-declaration-fires-clean = {
      expr = breaches {
        emits = [ "host" ];
        binds = [
          "host"
          "accessGroups"
        ];
        suppresses = [ ];
      } bindsFn;
      expected = [ ];
    };

    # ── THE RETIREMENT, AS CONSTRUCTIONS ──
    # The retired constructor keeps its arity (one argument) and mints a refusal, never an escape
    # record: no `opaque` or `__isPolicy` marker survives for a later reader to trust.
    test-the-retired-constructor-mints-no-escape-record = {
      expr =
        let
          r = genProgram.escape {
            name = "honest";
            fn = bindsFn;
            emits = [ "host" ];
            binds = [ "host" ];
            suppresses = [ ];
          };
        in
        {
          inherit (r) refused code;
          marked = r ? opaque || r ? __isPolicy;
        };
      expected = {
        refused = true;
        code = "policy-body/escape-retired";
        marked = false;
      };
    };
    test-a-bare-lambda-is-refused-at-registration-with-the-signpost-to-the-door = {
      expr =
        let
          r = genProgram.admit (c: [ ]);
        in
        {
          inherit (r) refused code;
          door = prelude.hasInfix "gen-rules door" r.message;
          escape = prelude.hasInfix "escape" r.message;
        };
      expected = {
        refused = true;
        code = "policy-body/constructor-not-manifest";
        door = true;
        escape = false;
      };
    };
    # A hand-rolled escape record is refused by name before any contract check: complete, missing
    # a field, or carrying an out-of-row one, it is retired, not malformed.
    test-a-hand-rolled-escape-record-is-refused-by-name-whatever-its-contract = {
      expr =
        map
          (
            r:
            code (
              genProgram.admit (
                {
                  opaque = true;
                  name = "hand-rolled";
                  fn = _: [ ];
                }
                // r
              )
            )
          )
          [
            {
              emits = [ ];
              binds = [ ];
              suppresses = [ ];
            }
            {
              emits = [ ];
              suppresses = [ ];
            }
            {
              emits = [ ];
              binds = [ ];
              suppresses = [ ];
              adaptArgs = _: { };
            }
          ];
      expected = [
        "policy-body/escape-retired"
        "policy-body/escape-retired"
        "policy-body/escape-retired"
      ];
    };

    # ── P-2 (exec gate): THE SHAPE ARM ──
    # A declaration outside the skeleton shape — an unknown ctor, or no ctor at all (what a raw
    # unwrapped v1 lambda returns) — is a TAGGED shape breach, never an internal crash blaming this
    # module. The green twin is the honest control above: the same check, skeleton-shaped
    # declarations, clean.
    test-p2-a-declaration-outside-the-skeleton-shape-is-a-tagged-shape-breach = {
      expr =
        map
          (breaches {
            emits = [ ];
            binds = [ ];
            suppresses = [ ];
          })
          [
            (_: [ { ctor = "frobnicate"; } ])
            (_: [ { modules = [ ]; } ])
          ];
      expected = [
        [
          {
            field = "shape";
            delta = "a declaration whose ctor is not a known constructor";
          }
        ]
        [
          {
            field = "shape";
            delta = "a declaration without a ctor";
          }
        ]
      ];
    };

    # ── P-3 (exec gate): FIELD TOTALITY AT RECORD LEVEL ──
    # The migration half-step: normal-form clauses beside a stale v1-style declared codomain.
    # The stale field is refused, never silently dropped — the derivation would otherwise read a
    # different answer than the author's declaration with nothing saying so.
    test-p3-a-declared-codomain-field-beside-normal-form-clauses-is-refused = {
      expr = {
        inherit
          (genProgram.admit {
            name = "half-migrated";
            clauses = [ ];
            binds = [ "accessGroups" ];
          })
          refused
          code
          witness
          ;
      };
      expected = {
        refused = true;
        code = "policy-body/skeleton-malformed";
        witness = [ "binds" ];
      };
    };
    test-control-p3-the-same-record-without-the-stale-field-is-admitted = {
      expr =
        (genProgram.admit {
          name = "half-migrated";
          clauses = [ ];
          declared = null;
        }).refused;
      expected = false;
    };
  };
}
