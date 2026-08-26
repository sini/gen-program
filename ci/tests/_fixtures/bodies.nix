# THE CORPUS, TRANSCRIBED — the seven nix-config policies of the spec's O3 table, written in the
# normal form under the substrate constructor names, each with a REAL (non-sentinel) firing
# context whose guards take their true branches. Transcribed from source (nix-config
# modules/den: policies/fleet.nix, defaults.nix, classes/home-platform.nix,
# batteries/nix-on-droid.nix); the free expressions carry the originals' computation shapes.
#
# `observe` is the TEST-SIDE firing: it instantiates every skeleton against the context (the item
# joins the scope under an iteration), applies the guards, applies payload values and free
# targets — forcing them, so a transcription that could not actually fire fails here — and
# collects the codomain the firing PRODUCED. The oracle is that the walk's derivation, which
# fires nothing, equals this observation at a real context. The observer deliberately spells the
# constructor→kind mapping out by hand rather than importing the library's row table: it is the
# firing's own report, not a second read of the thing under test.
{ prelude, genProgram }:
let
  inherit (builtins)
    attrNames
    attrValues
    concatMap
    deepSeq
    elem
    filter
    mapAttrs
    sort
    ;

  sortUnique = xs: sort (a: b: a < b) (prelude.unique xs);

  observe =
    b: ctx:
    let
      placed = concatMap (
        c:
        if c ? over then
          concatMap (
            item:
            map (s: {
              inherit s;
              scope = ctx // {
                inherit item;
              };
            }) c.emit
          ) (c.over ctx)
        else
          [
            {
              s = c;
              scope = ctx;
            }
          ]
      ) b.clauses;
      live = filter (x: !(x.s ? when) || x.s.when x.scope) placed;
      # The firing is real: payload values and free targets are applied AND forced.
      firedPayload =
        x: deepSeq (attrValues (mapAttrs (_: f: f x.scope) x.s.payload)) (attrNames x.s.payload);
      firedTarget = x: deepSeq (x.s.target x.scope) [ ];
    in
    {
      emits = sortUnique (
        concatMap (
          x:
          if x.s.ctor == "member" then
            [ x.s.kind ]
          else if x.s.ctor == "deliver" then
            [ "delivery" ]
          else if x.s.ctor == "edge" then
            [ "edge" ] ++ firedTarget x
          else if x.s.ctor == "realize" then
            [ "instantiate" ] ++ firedTarget x
          else
            [ ]
        ) live
      );
      binds = sortUnique (concatMap (x: if x.s.ctor == "member" then firedPayload x else [ ]) live);
      suppresses = sortUnique (
        concatMap (x: if x.s.ctor == "suppress" then [ x.s.target ] else [ ]) live
      );
    };

  # ── 1 · to-fleet (fleet.nix) — one emission, unconditional ──
  toFleet = genProgram.body {
    name = "to-fleet";
    clauses = [
      (genProgram.emit {
        ctor = "member";
        kind = "fleet";
        payload = {
          fleet = _: { name = "fleet"; };
          secretsConfig = { config, ... }: config.den.secretsConfig;
        };
      })
    ];
  };
  toFleetCtx = {
    config.den.secretsConfig = {
      provider = "sops";
    };
  };

  # ── 2 · fleet-to-envs (fleet.nix) — fan out per registered environment ──
  fleetToEnvs = genProgram.body {
    name = "fleet-to-envs";
    clauses = [
      (genProgram.forEach {
        over = { environments, ... }: attrValues environments;
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
  fleetToEnvsCtx = {
    environments.prod = {
      name = "prod";
    };
  };

  # ── 3 · env-to-hosts (fleet.nix:50-89) — THE §2.7 WITNESS, the corpus's heaviest body ──
  # Nested concatMap over the host registry, dynamic ${} lookup, or-defaults and union/filter
  # set algebra ALL live inside `over`'s free expression, where the algebra never interprets
  # them. The guard sits on each skeleton (the item joins the scope) — a ForEach-level guard
  # does not exist, per the grammar's F1 amendment; the two skeletons carry it by duplication
  # with meaning unchanged.
  envToHostsGuard =
    { environment, item, ... }:
    (item.hostCfg.environment or "prod") == environment.name && item.hostCfg.intoAttr != [ ];
  envToHosts = genProgram.body {
    name = "env-to-hosts";
    clauses = [
      (genProgram.forEach {
        over =
          {
            environment,
            fleet,
            den,
            ...
          }:
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
          ) (attrNames (den.hosts or { }));
        emit = [
          {
            ctor = "member";
            kind = "host";
            when = envToHostsGuard;
            payload = {
              host = { item, ... }: item.hostCfg;
              accessGroups = { item, ... }: item.accessGroups;
            };
          }
          {
            ctor = "realize";
            when = envToHostsGuard;
            target = { item, ... }: item.hostCfg;
          }
        ];
      })
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

  # ── 4 · user-aspect-auto-include (defaults.nix:169) — free include target, live in the
  # reference corpus: the target is context-dependent, which the ruled D3 dial admits (excludes
  # only are literal) ──
  userAspectAutoInclude = genProgram.body {
    name = "user-aspect-auto-include";
    clauses = [
      (genProgram.emit {
        ctor = "edge";
        when =
          {
            host,
            user,
            den,
            ...
          }:
          den.aspects ? ${host.name} && den.aspects.${host.name} ? ${user.name};
        target =
          {
            host,
            user,
            den,
            ...
          }:
          den.aspects.${host.name}.${user.name};
      })
    ];
  };
  userAspectAutoIncludeCtx = {
    host.name = "blade";
    user.name = "sini";
    den.aspects.blade.sini = {
      name = "blade-sini";
    };
  };

  # ── 5 · primary-user-for-owner (defaults.nix:189) — owner-equality guard, fixed target ──
  primaryUserForOwner = genProgram.body {
    name = "primary-user-for-owner";
    clauses = [
      (genProgram.emit {
        ctor = "edge";
        when = { host, user, ... }: user.name == (host.system-owner or null);
        target = { den, ... }: den.batteries.primary-user;
      })
    ];
  };
  primaryUserForOwnerCtx = {
    host.system-owner = "sini";
    user.name = "sini";
    den.batteries.primary-user = {
      name = "primary-user";
    };
  };

  # ── 6 · homeAarch64-to-hm (home-platform.nix) — a delivery, keys fixed, guard free ──
  homeAarch64ToHm = genProgram.body {
    name = "homeAarch64-to-hm";
    clauses = [
      (genProgram.emit {
        ctor = "deliver";
        when = { host, ... }: prelude.hasPrefix "aarch64-" host.system;
        payload = {
          fromClass = _: "homeAarch64";
          intoClass = _: "homeManager";
          path = _: [ ];
        };
      })
    ];
  };
  homeAarch64ToHmCtx = {
    host.system = "aarch64-darwin";
  };

  # ── 7 · drop-user-to-host-on-droid (nix-on-droid.nix) — a literal suppression ──
  dropUserToHostOnDroid = genProgram.body {
    name = "drop-user-to-host-on-droid";
    clauses = [
      (genProgram.emit {
        ctor = "suppress";
        when = { host, ... }: host.class == "droid";
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
