# ORACLE O1 — EVERY REFUSAL FIRES, WITH ITS MINIMALLY-DIFFERING GREEN TWIN IN THE SAME RUN.
#
# Each of the four manifestness violations (nzu9's V-rows) is seeded in its minimal shape and
# refused BY NAME; beside each sits an admitted body differing only in the violating slot — an
# absence claim without its positive control is not a measurement. The F1 structural code gets
# the same treatment: the seeded `when`-on-ForEach is the spec's own v0 witness defect, and its
# green control is the repaired witness itself (the corpus fixture's env-to-hosts).
#
# ★ REFUSALS ARE VALUES, NOT THROWS — asserted as such: `tryEval` succeeds on every one of them
# (`tryEval` cannot catch every failure form, which is why the discipline is tagged values in the
# type), the code names the violated slot, the blamed party is the AUTHOR at every row, and the
# four V-row messages carry the signpost to the declared escape — the refusal is how the compat
# channel is discovered rather than fought.
{
  genProgram,
  prelude,
  ...
}:
let
  fixtures = import ./_fixtures/bodies.nix { inherit prelude genProgram; };

  # V1 — constructor in a field value: anything context-shaped at the ctor slot.
  v1Red = genProgram.emit {
    ctor = ctx: if ctx.wantsMember then "member" else "edge";
    kind = "host";
    payload = {
      host = { host, ... }: host;
    };
  };
  v1Green = genProgram.emit {
    ctor = "member";
    kind = "host";
    payload = {
      host = { host, ... }: host;
    };
  };

  # V2 — the `{...}@ctx` pass-through: a bare function at the payload slot, the shape measured
  # live at nested-ctx.nix:18 and named-provider.nix:58 (it re-emits the whole context).
  v2Red = genProgram.emit {
    ctor = "member";
    kind = "host";
    payload = ctx: ctx;
  };
  v2Green = genProgram.emit {
    ctor = "member";
    kind = "host";
    payload = {
      host = ctx: ctx.host;
    };
  };

  # V3 — computed payload keys: a spine that does not force at construction (a context-shaped
  # merge). The green twin is Q3's registration-fixed reading exercised: a merge whose spine DOES
  # force at construction is ADMITTED, and R3 fires only on does-not-force.
  v3Red = genProgram.emit {
    ctor = "member";
    kind = "host";
    payload = {
      static = _: 1;
    }
    // (throw "a context-shaped merge: this spine cannot force before a context exists");
  };
  v3Green = genProgram.emit {
    ctor = "member";
    kind = "host";
    payload = {
      static = _: 1;
    }
    // {
      fromRegistry = _: 2;
    };
  };

  # V4 — dynamic exclude target: computed from the scope rather than fixed at registration.
  v4Red = genProgram.emit {
    ctor = "suppress";
    target = { host, ... }: "user-to-${host.class}";
  };
  v4Green = genProgram.emit {
    ctor = "suppress";
    target = "user-to-host";
  };

  # F1 — the out-of-row field: `when` on ForEach is the v0 witness's own defect (a per-item
  # guard is the skeleton-level `when`; the item already joins the scope).
  f1Red = genProgram.forEach {
    over = { environments, ... }: builtins.attrValues environments;
    when = { item, ... }: item.enabled;
    emit = [
      {
        ctor = "member";
        kind = "environment";
        payload = {
          environment = { item, ... }: item;
        };
      }
    ];
  };

  vReds = [
    v1Red
    v2Red
    v3Red
    v4Red
  ];
in
{
  flake.tests.bodyRefusals = {
    # ── THE FOUR V-ROWS, RED THEN GREEN ──
    test-v1-a-context-shaped-constructor-is-refused-by-name = {
      expr = {
        inherit (v1Red) refused code blamed;
      };
      expected = {
        refused = true;
        code = "policy-body/constructor-not-manifest";
        blamed = "author";
      };
    };
    test-control-v1-the-twin-with-a-literal-constructor-is-admitted = {
      expr = v1Green.refused or false;
      expected = false;
    };

    test-v2-the-context-pass-through-payload-is-refused-by-name = {
      expr = {
        inherit (v2Red) refused code blamed;
      };
      expected = {
        refused = true;
        code = "policy-body/payload-not-keyed";
        blamed = "author";
      };
    };
    test-control-v2-the-twin-with-keyed-function-values-is-admitted = {
      expr = v2Green.refused or false;
      expected = false;
    };

    test-v3-a-spine-that-cannot-force-at-construction-is-refused-by-name = {
      expr = {
        inherit (v3Red) refused code blamed;
      };
      expected = {
        refused = true;
        code = "policy-body/payload-keys-unfixed";
        blamed = "author";
      };
    };
    test-control-v3-the-registration-fixed-merge-is-admitted-with-both-keys-read = {
      # Q3's extension, demonstrated: the merge shape nzu9's V3 motivated is admitted whenever
      # the spine forces at construction — and the walk reads the merged spine whole.
      expr = {
        refused = v3Green.refused or false;
        keys = builtins.attrNames v3Green.payload;
      };
      expected = {
        refused = false;
        keys = [
          "fromRegistry"
          "static"
        ];
      };
    };

    test-v4-a-computed-suppress-target-is-refused-by-name = {
      expr = {
        inherit (v4Red) refused code blamed;
      };
      expected = {
        refused = true;
        code = "policy-body/exclude-target-unfixed";
        blamed = "author";
      };
    };
    test-control-v4-the-twin-with-a-literal-target-is-admitted = {
      expr = v4Green.refused or false;
      expected = false;
    };

    # ── F1: THE STRUCTURAL CODE, RED THEN GREEN ──
    test-f1-when-on-foreach-is-refused-as-out-of-row-never-ignored = {
      expr = {
        inherit (f1Red) refused code;
        witness = f1Red.witness;
      };
      expected = {
        refused = true;
        code = "policy-body/skeleton-malformed";
        witness = [ "when" ];
      };
    };
    test-control-f1-the-repaired-witness-parses-under-its-own-grammar = {
      expr = fixtures.corpus.env-to-hosts.body.refused or false;
      expected = false;
    };

    # ── REFUSALS ARE VALUES ──
    test-every-seeded-refusal-is-a-tagged-value-tryeval-succeeds-on-all-five = {
      expr = map (r: (builtins.tryEval r).success) (vReds ++ [ f1Red ]);
      expected = [
        true
        true
        true
        true
        true
      ];
    };
    test-the-four-v-row-messages-carry-the-signpost-to-the-declared-escape = {
      expr = map (r: prelude.hasInfix "escape" r.message) vReds;
      expected = [
        true
        true
        true
        true
      ];
    };

    # ── THE FREE POSITIONS STAY FREE ──
    # The refusal surface must not over-reach: an edge target is FREE by the ruled D3 dial
    # (excludes only are literal), so a context-dependent include target — live in the reference
    # corpus — is admitted, in the same run that refuses V4 one row up.
    test-control-a-context-dependent-edge-target-is-admitted-d3-is-excludes-only = {
      expr =
        (genProgram.emit {
          ctor = "edge";
          target = { den, host, ... }: den.aspects.${host.name};
        }).refused or false;
      expected = false;
    };
  };
}
