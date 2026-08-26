# ORACLE O4 — THE ESCAPE'S CODOMAIN CONTRACT IS CONTRACTED AT EVERY FIRING.
#
# The declared escape is the v1-lambda compat channel, and the per-firing check is the whole
# difference between its declaration and the five inert nix-config declarations it replaces
# (ADR-0008: the licence is the contract, and an uncontracted projection rots into vacuity).
# All three directions are seeded — an emission outside `emits`, a member-binding key outside
# `binds`, an exclusion outside `suppresses` — and the green control is the same body under its
# honest declaration, firing clean in the same run.
#
# ★ THE PRICES ARE ASSERTED AS CONSTRUCTIONS, NOT DOCUMENTATION: the three codomain fields are
# REQUIRED and total (readable in-language from `functionArgs`, the mkModel precedent), the
# `opaque = true` marker is queryable, and a bare lambda without the marker is refused at
# registration with the refusal pointing here — no silent entry.
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

  # Emission outside `emits`: declares only "edge", fires a member of kind "host".
  emitsBreach = genProgram.escape {
    name = "seeded-emits-breach";
    emits = [ "edge" ];
    binds = [ ];
    suppresses = [ ];
    fn = _: [
      {
        ctor = "member";
        kind = "host";
        payload = { };
      }
    ];
  };

  # Member-binding key outside `binds`: declares host, also fires accessGroups.
  bindsBreach = genProgram.escape {
    name = "seeded-binds-breach";
    emits = [ "host" ];
    binds = [ "host" ];
    suppresses = [ ];
    fn = c: [
      {
        ctor = "member";
        kind = "host";
        payload = {
          host = c.host;
          accessGroups = [ "admins" ];
        };
      }
    ];
  };

  # Exclusion outside `suppresses`.
  suppressesBreach = genProgram.escape {
    name = "seeded-suppresses-breach";
    emits = [ ];
    binds = [ ];
    suppresses = [ ];
    fn = _: [
      {
        ctor = "suppress";
        target = "user-to-host";
      }
    ];
  };

  # The green control: the binds-breach body under its HONEST declaration.
  honest = genProgram.escape {
    name = "honest";
    emits = [ "host" ];
    binds = [
      "host"
      "accessGroups"
    ];
    suppresses = [ ];
    fn = bindsBreach.fn;
  };
in
{
  flake.tests.bodyEscape = {
    # ── THE THREE SEEDED BREACHES, EACH NAMED WITH ITS FIELD AND DELTA ──
    test-o4-an-emission-outside-emits-is-refused-at-the-firing = {
      expr = {
        inherit (genProgram.fireEscape emitsBreach ctx) code witness;
      };
      expected = {
        code = "policy-body/codomain-breach";
        witness = {
          site = "seeded-emits-breach";
          breaches = [
            {
              field = "emits";
              delta = "host";
            }
          ];
        };
      };
    };
    test-o4-a-member-binding-key-outside-binds-is-refused-at-the-firing = {
      expr = (genProgram.fireEscape bindsBreach ctx).witness.breaches;
      expected = [
        {
          field = "binds";
          delta = "accessGroups";
        }
      ];
    };
    test-o4-an-exclusion-outside-suppresses-is-refused-at-the-firing = {
      expr = (genProgram.fireEscape suppressesBreach ctx).witness.breaches;
      expected = [
        {
          field = "suppresses";
          delta = "user-to-host";
        }
      ];
    };

    # ── THE GREEN CONTROL: THE HONEST DECLARATION FIRES CLEAN, SAME BODY, SAME RUN ──
    test-control-o4-the-same-body-under-its-honest-declaration-fires-clean = {
      expr = genProgram.fireEscape honest ctx;
      expected = [
        {
          ctor = "member";
          kind = "host";
          payload = {
            host = {
              name = "web1";
            };
            accessGroups = [ "admins" ];
          };
        }
      ];
    };

    # ── THE CODOMAIN IS READ, NOT COMPUTED, ON THE ESCAPE ──
    test-derive-codomain-reads-the-declared-contract-on-an-escape = {
      expr = genProgram.deriveCodomain honest;
      expected = {
        emits = [ "host" ];
        binds = [
          "accessGroups"
          "host"
        ];
        suppresses = [ ];
      };
    };

    # ── THE PRICES, AS CONSTRUCTIONS ──
    test-the-three-codomain-fields-are-required-with-no-defaults = {
      expr = builtins.functionArgs genProgram.escape;
      expected = {
        name = false;
        fn = false;
        emits = false;
        binds = false;
        suppresses = false;
      };
    };
    test-the-opaque-marker-is-queryable-on-the-constructed-escape = {
      expr = {
        inherit (honest) opaque __isPolicy;
      };
      expected = {
        opaque = true;
        __isPolicy = true;
      };
    };
    test-a-bare-lambda-without-the-marker-is-refused-at-registration = {
      expr =
        let
          r = genProgram.admit (c: [ ]);
        in
        {
          inherit (r) refused code;
          signpost = prelude.hasInfix "escape" r.message;
        };
      expected = {
        refused = true;
        code = "policy-body/constructor-not-manifest";
        signpost = true;
      };
    };
    test-a-hand-rolled-escape-missing-a-contract-field-is-refused-not-defaulted = {
      # `[ ]` is written, not defaulted — absence is a decision, and an absent field is a
      # malformation rather than permissiveness.
      expr = {
        inherit
          (genProgram.admit {
            opaque = true;
            name = "hand-rolled";
            fn = _: [ ];
            emits = [ ];
            suppresses = [ ];
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
    test-control-the-complete-hand-rolled-escape-is-admitted = {
      expr =
        (genProgram.admit {
          opaque = true;
          name = "hand-rolled";
          fn = _: [ ];
          emits = [ ];
          binds = [ ];
          suppresses = [ ];
        }).refused;
      expected = false;
    };
  };
}
