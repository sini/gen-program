# THE CORPUS, TRANSCRIBED — the seven nix-config policies of the spec's O3 table, written in the
# normal form under the substrate constructor names, each with a REAL (non-sentinel) firing
# context whose guards take their true branches. Transcribed from source (nix-config
# modules/den: policies/fleet.nix, defaults.nix, classes/home-platform.nix,
# batteries/nix-on-droid.nix).
#
# ★ TERMS ONLY (den-hoag-lwbb1 unit 3, spec §2.11). Three policies are expressible in the term
# algebra's vocabulary and are written as terms. The other four compute with what the vocabulary
# does not have — or-defaults with `unique`/`filter` inside `over`, a dynamic attribute path, a
# comparison of two reads, `hasPrefix` — so they CROSS THE DOOR as door clauses: a first-order
# condition (`has` over the closure's formals), the body `ref r`, and the codomain contract the
# framework declares at registration. The closure itself lives behind `door` below, the
# test-side stand-in for the framework's door, which is the only place one is applied.
#
# `observe` is the TEST-SIDE firing: it fires the body through the interpreter at the context,
# forces every payload value and target the firing produced — so a transcription that could not
# actually fire fails here — and collects the codomain the firing PRODUCED. The oracle is that the
# walk's derivation, which fires nothing, equals this observation at a real context. The observer
# deliberately spells the constructor→kind mapping out by hand rather than importing the library's
# row table: it is the firing's own report, not a second read of the thing under test.
{
  prelude,
  genProgram,
  T,
}:
let
  inherit (builtins)
    attrNames
    attrValues
    concatMap
    deepSeq
    elem
    filter
    sort
    ;
  t = T.term;

  sortUnique = xs: sort (a: b: a < b) (prelude.unique xs);

  # A door registration's identifier, as the framework's lowering mints it (`refId`).
  regId =
    site: reads:
    (T.refId {
      declared = { inherit site reads; };
    }).right;

  # The four closures that cross the door, keyed by their registration identifier.
  closures = {
    ${
      regId "fleet.nix:50" [
        "environment"
        "fleet"
        "den"
      ]
    } =
      envToHostsFn;
    ${
      regId "defaults.nix:169" [
        "host"
        "user"
        "den"
      ]
    } =
      userAspectAutoIncludeFn;
    ${
      regId "defaults.nix:189" [
        "host"
        "user"
        "den"
      ]
    } =
      primaryUserForOwnerFn;
    ${regId "home-platform.nix" [ "host" ]} = homeAarch64ToHmFn;
  };
  # The framework's door, test-side: it applies the registered closure to the context and hands its
  # declarations back as data. It is the one place a closure is applied.
  door =
    { id, context, ... }:
    {
      right = {
        output = closures.${id} context;
        scope = { };
      };
    };

  observe =
    b: ctx:
    let
      fired = genProgram.groundInstances {
        body = b;
        context = ctx;
        inherit door;
      };
      # The firing is real: payload values and targets are forced.
      firedPayload = d: deepSeq (attrValues d.payload) (attrNames d.payload);
      firedTarget = d: deepSeq d.target [ ];
    in
    {
      emits = sortUnique (
        concatMap (
          d:
          if d.ctor == "member" then
            [ d.kind ]
          else if d.ctor == "deliver" then
            deepSeq (firedPayload d) [ "delivery" ]
          else if d.ctor == "edge" then
            [ "edge" ] ++ firedTarget d
          else if d.ctor == "realize" then
            [ "instantiate" ] ++ firedTarget d
          else
            [ ]
        ) fired
      );
      binds = sortUnique (concatMap (d: if d.ctor == "member" then firedPayload d else [ ]) fired);
      suppresses = sortUnique (concatMap (d: if d.ctor == "suppress" then [ d.target ] else [ ]) fired);
    };

  # A door clause: the condition covers the closure's formals; the contract is declared.
  doorClause =
    id: formals: contract:
    {
      when = t.all (map t.has formals);
      body = t.ref id;
    }
    // contract;

  # ── 1 · to-fleet (fleet.nix) — one emission, unconditional ── (terms)
  toFleet = genProgram.body {
    name = "to-fleet";
    declared = [ "config" ];
    clauses = [
      (genProgram.emit {
        ctor = "member";
        kind = "fleet";
        when = t.has "config";
        payload = {
          fleet = t.lit { name = "fleet"; };
          secretsConfig = t.readCtx "config" [
            "den"
            "secretsConfig"
          ];
        };
      })
    ];
  };
  toFleetCtx = {
    config.den.secretsConfig = {
      provider = "sops";
    };
  };

  # ── 2 · fleet-to-envs (fleet.nix) — fan out per registered environment ── (terms)
  # `over` reads `environments`, so its derived condition is `has environments`; the item joins
  # the scope, and the per-item guard is the skeleton-level `when` (the grammar's F1 amendment).
  fleetToEnvs = genProgram.body {
    name = "fleet-to-envs";
    declared = [ "environments" ];
    clauses = [
      (genProgram.forEach {
        over = t.apply "attrNames" [ (t.readCtx "environments" [ ]) ];
        emit = [
          {
            ctor = "member";
            kind = "environment";
            when = t.has "environments";
            payload = {
              environment = t.apply "getAttr" [
                (t.readCtx "item" [ ])
                (t.readCtx "environments" [ ])
              ];
            };
          }
        ];
      })
    ];
  };
  fleetToEnvsCtx = {
    environments.prod = {
      name = "prod";
    };
  };

  # ── 3 · env-to-hosts (fleet.nix:50-89) — the corpus's heaviest body ── (door)
  # Nested concatMap over the host registry, dynamic ${} lookup, or-defaults and union/filter
  # set algebra: the vocabulary has none of them, so the closure crosses the door with its
  # contract declared. `binds` carries the adjudicated `host` key (body-corpus.nix).
  envToHostsFn =
    {
      environment,
      fleet,
      den,
      ...
    }:
    concatMap
      (
        item:
        if (item.hostCfg.environment or "prod") == environment.name && item.hostCfg.intoAttr != [ ] then
          [
            {
              ctor = "member";
              kind = "host";
              payload = {
                host = item.hostCfg;
                inherit (item) accessGroups;
              };
            }
            {
              ctor = "realize";
              target = item.hostCfg;
            }
          ]
        else
          [ ]
      )
      (
        concatMap (
          system:
          map (
            hostName:
            let
              hostCfg = den.hosts.${system}.${hostName};
              envGrant = (fleet.user-access.by-environment.${environment.name} or { groups = [ ]; }).groups;
              envGate = environment.system-access-groups or [ ];
              hostGrant = (fleet.user-access.by-host.${hostName} or { groups = [ ]; }).groups;
              hostGate = hostCfg.system-access-groups;
              effectiveGate = prelude.unique (envGate ++ hostGate);
              allGrants = prelude.unique (envGrant ++ hostGrant ++ hostGate);
            in
            {
              inherit hostCfg;
              accessGroups =
                if effectiveGate == [ ] then allGrants else filter (g: elem g effectiveGate) allGrants;
            }
          ) (attrNames (den.hosts.${system} or { }))
        ) (attrNames (den.hosts or { }))
      );
  envToHosts = genProgram.body {
    name = "env-to-hosts";
    declared = [
      "environment"
      "fleet"
      "den"
    ];
    clauses = [
      (doorClause
        (regId "fleet.nix:50" [
          "environment"
          "fleet"
          "den"
        ])
        [ "environment" "fleet" "den" ]
        {
          emits = [
            "host"
            "instantiate"
          ];
          binds = [
            "accessGroups"
            "host"
          ];
          suppresses = [ ];
        }
      )
    ];
  };
  envToHostsCtx = {
    environment = {
      name = "prod";
      system-access-groups = [ "admins" ];
    };
    fleet.user-access = {
      by-environment.prod.groups = [ "admins" ];
      by-host = { };
    };
    den.hosts.x86_64-linux.web1 = {
      name = "web1";
      environment = "prod";
      intoAttr = [ "nixosConfigurations" ];
      system-access-groups = [ "admins" ];
    };
  };

  # ── 4 · user-aspect-auto-include (defaults.nix:169) — a dynamic attribute path ── (door)
  userAspectAutoIncludeFn =
    {
      host,
      user,
      den,
      ...
    }:
    if den.aspects ? ${host.name} && den.aspects.${host.name} ? ${user.name} then
      [
        {
          ctor = "edge";
          target = den.aspects.${host.name}.${user.name};
        }
      ]
    else
      [ ];
  userAspectAutoInclude = genProgram.body {
    name = "user-aspect-auto-include";
    declared = [
      "host"
      "user"
      "den"
    ];
    clauses = [
      (doorClause
        (regId "defaults.nix:169" [
          "host"
          "user"
          "den"
        ])
        [ "host" "user" "den" ]
        {
          emits = [ "edge" ];
          binds = [ ];
          suppresses = [ ];
        }
      )
    ];
  };
  userAspectAutoIncludeCtx = {
    host.name = "blade";
    user.name = "sini";
    den.aspects.blade.sini = {
      name = "blade-sini";
    };
  };

  # ── 5 · primary-user-for-owner (defaults.nix:189) — compares two reads ── (door)
  primaryUserForOwnerFn =
    {
      host,
      user,
      den,
      ...
    }:
    if user.name == (host.system-owner or null) then
      [
        {
          ctor = "edge";
          target = den.batteries.primary-user;
        }
      ]
    else
      [ ];
  primaryUserForOwner = genProgram.body {
    name = "primary-user-for-owner";
    declared = [
      "host"
      "user"
      "den"
    ];
    clauses = [
      (doorClause
        (regId "defaults.nix:189" [
          "host"
          "user"
          "den"
        ])
        [ "host" "user" "den" ]
        {
          emits = [ "edge" ];
          binds = [ ];
          suppresses = [ ];
        }
      )
    ];
  };
  primaryUserForOwnerCtx = {
    host.system-owner = "sini";
    user.name = "sini";
    den.batteries.primary-user = {
      name = "primary-user";
    };
  };

  # ── 6 · homeAarch64-to-hm (home-platform.nix) — `hasPrefix` (unifying spec OQ6) ── (door)
  homeAarch64ToHmFn =
    { host, ... }:
    if prelude.hasPrefix "aarch64-" host.system then
      [
        {
          ctor = "deliver";
          payload = {
            fromClass = "homeAarch64";
            intoClass = "homeManager";
            path = [ ];
          };
        }
      ]
    else
      [ ];
  homeAarch64ToHm = genProgram.body {
    name = "homeAarch64-to-hm";
    declared = [ "host" ];
    clauses = [
      (doorClause (regId "home-platform.nix" [ "host" ]) [ "host" ] {
        emits = [ "delivery" ];
        binds = [ ];
        suppresses = [ ];
      })
    ];
  };
  homeAarch64ToHmCtx = {
    host.system = "aarch64-darwin";
  };

  # ── 7 · drop-user-to-host-on-droid (nix-on-droid.nix) — a literal suppression ── (terms)
  dropUserToHostOnDroid = genProgram.body {
    name = "drop-user-to-host-on-droid";
    declared = [ "host" ];
    clauses = [
      (genProgram.emit {
        ctor = "suppress";
        when = t.eq [
          "host"
          "class"
        ] "droid";
        target = "user-to-host";
      })
    ];
  };
  dropUserToHostOnDroidCtx = {
    host.class = "droid";
  };
in
{
  inherit observe sortUnique;

  corpus = {
    to-fleet = {
      body = toFleet;
      ctx = toFleetCtx;
      derived = {
        emits = [ "fleet" ];
        binds = [
          "fleet"
          "secretsConfig"
        ];
        suppresses = [ ];
      };
    };
    fleet-to-envs = {
      body = fleetToEnvs;
      ctx = fleetToEnvsCtx;
      derived = {
        emits = [ "environment" ];
        binds = [ "environment" ];
        suppresses = [ ];
      };
    };
    env-to-hosts = {
      body = envToHosts;
      ctx = envToHostsCtx;
      derived = {
        emits = [
          "host"
          "instantiate"
        ];
        binds = [
          "accessGroups"
          "host"
        ];
        suppresses = [ ];
      };
    };
    user-aspect-auto-include = {
      body = userAspectAutoInclude;
      ctx = userAspectAutoIncludeCtx;
      derived = {
        emits = [ "edge" ];
        binds = [ ];
        suppresses = [ ];
      };
    };
    primary-user-for-owner = {
      body = primaryUserForOwner;
      ctx = primaryUserForOwnerCtx;
      derived = {
        emits = [ "edge" ];
        binds = [ ];
        suppresses = [ ];
      };
    };
    homeAarch64-to-hm = {
      body = homeAarch64ToHm;
      ctx = homeAarch64ToHmCtx;
      derived = {
        emits = [ "delivery" ];
        binds = [ ];
        suppresses = [ ];
      };
    };
    drop-user-to-host-on-droid = {
      body = dropUserToHostOnDroid;
      ctx = dropUserToHostOnDroidCtx;
      derived = {
        emits = [ ];
        binds = [ ];
        suppresses = [ "user-to-host" ];
      };
    };
  };
}
