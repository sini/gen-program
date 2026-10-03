# THE TERMS-ONLY GATING ORACLE (den-hoag-lwbb1 unit 3, U3a; den-ag-design
# specs/2026-10-02-gen-program-terms-only-spec.md §3a, with the spec gate's conditions C1, C2, P4,
# P7 and P9).
#
# Every free slot of a policy body is a term; the walk checks each clause under the body's one
# declared set `D`; `groundInstances` resolves an admitted body at a context under that same `D`
# and resolves a door clause through the framework's door; rules and firings carry identities
# minted through the one authority; and `declaration` gains the literal tier, a `when` term lowered
# to `pos`/`neg`. Each cell below has been driven red against the construction it names (the
# landing report's plant table).
{
  genProgram,
  T,
  ...
}:
let
  t = T.term;
  gp = genProgram;
  code = r: if builtins.isAttrs r && (r.refused or false) then r.code else "admitted";
  # Fired declarations without their identity, for cells about what fired.
  strip =
    xs:
    if builtins.isList xs then
      map (x: if builtins.isAttrs x then builtins.removeAttrs x [ "__mint" ] else x) xs
    else if builtins.isAttrs xs && xs ? code then
      xs.code
    else
      xs;
  minted = x: (x.__mint or { }).minted or null;
  D = [
    "thimble"
    "bobbin"
  ];
  src = k: "entity:" + builtins.hashString "sha256" k;
  rDoor =
    (T.refId {
      declared = {
        site = "mod:aspects.tuck";
        reads = [ "host" ];
      };
    }).right;
  rNested =
    (T.refId {
      nested = {
        outer = rDoor;
        sources = {
          host = src "h";
        };
        position = [
          "includes"
          0
        ];
        reads = null;
      };
    }).right;
  bodyOf =
    declared: clauses:
    gp.body {
      name = "cell";
      inherit declared clauses;
    };
  tuck = {
    ctor = "member";
    kind = "tuck";
    when = t.has "thimble";
    payload.description = t.concat [
      (t.lit "tuck-")
      (t.readCtx "thimble" [ ])
    ];
  };
  tuckBody = bodyOf D [ tuck ];
  fire =
    b: ctx: srcs:
    gp.groundInstances { sources = srcs; } ctx b;
  doorClause = {
    when = t.has "host";
    body = t.ref rDoor;
    emits = [ "host" ];
    binds = null;
    suppresses = [ ];
  };
  # The framework's door, stubbed: the outer registration answers a nested door clause and a fired
  # member, and hands back a scope carrying the nested registration's captured value; the nested
  # one answers a suppression naming what it was handed.
  stubDoor =
    a:
    if a.id == rDoor then
      {
        right = {
          output = [
            {
              when = t.always;
              body = t.ref rNested;
              emits = [ ];
              binds = [ ];
              suppresses = [ ];
            }
            {
              ctor = "member";
              kind = "host";
              payload.host = a.context.host;
            }
          ];
          scope.${rNested} = "CLOSURE-MARKER";
        };
      }
    else
      {
        right = {
          output = [
            {
              ctor = "suppress";
              target = "captured:${toString a.captured}";
            }
          ];
          scope = { };
        };
      };
  hostBody = bodyOf [ "host" ] [ doorClause ];
  # A door whose output carries one nested door clause, `nested`.
  doorAnswering = nested: _: {
    right = {
      output = [ nested ];
      scope = { };
    };
  };
  decl = d: gp.declaration (removeAttrs d [ "head" ]) [ "bolt" ] d.head;
  modelOf =
    ds:
    gp.model {
      program = gp.program [ "bolt" ] (map (d: { relata = [ "bolt" ]; } // d) ds);
      interpretation = [ ];
      prior = null;
      complete = true;
    };
  # C105's gusset/collar shape: `yoke` takes the guard under test.
  c105 = guard: [
    { head = "gusset:bolt"; }
    {
      head = "gusset-held:bolt";
      pos = [ "gusset:bolt" ];
      neg = [ "unpicked-gusset:bolt" ];
    }
    ({ head = "yoke:bolt"; } // guard)
    { head = "lining:bolt"; }
    {
      head = "collar:bolt";
      when = t.all [
        (t.has "lining:bolt")
        (t.not (t.has "unpicked-lining:bolt"))
      ];
    }
  ];
  ans =
    m:
    map (h: (m.resolve h).included) [
      "yoke:bolt"
      "collar:bolt"
    ];
  ruleMintOf = b: if b ? clauses then minted (builtins.head b.clauses) else null;
  refusesCatchably = e: !(builtins.tryEval (builtins.deepSeq e true)).success;

  environments =
    bodyOf
      [ "environments" ]
      [
        {
          over = t.readCtx "environments" [ ];
          emit = [
            {
              ctor = "member";
              kind = "environment";
              payload.environment = t.readCtx "item" [ ];
            }
          ];
        }
      ];
in
{
  flake.tests.termsOnly = {
    # ── THE SLOTS ARE TERMS, CHECKED UNDER ONE D ──
    test-payload-term-admitted = {
      expr = code (
        bodyOf
          [ "config" ]
          [
            {
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
            }
          ]
      );
      expected = "admitted";
    };
    test-function-payload-refused = {
      expr = code (
        bodyOf null [
          {
            ctor = "member";
            kind = "fleet";
            payload.x = _: 1;
          }
        ]
      );
      expected = "policy-body/term-function";
    };
    test-function-when-refused = {
      expr = code (
        bodyOf null [
          {
            ctor = "suppress";
            when = _: true;
            target = "x";
          }
        ]
      );
      expected = "policy-body/term-function";
    };
    test-unsafe-read-refused = {
      expr = code (bodyOf D [ (tuck // { when = t.always; }) ]);
      expected = "policy-body/unsafe-read";
    };
    test-safe-read-admitted = {
      expr = code tuckBody;
      expected = "admitted";
    };
    test-undeclared-did-you-mean = {
      expr =
        let
          r = bodyOf D [ (tuck // { when = t.has "thimbel"; }) ];
        in
        [
          (code r)
          (builtins.match ".*did you mean one of: thimble, bobbin.*" (r.message or "") != null)
        ];
      expected = [
        "policy-body/undeclared-name"
        true
      ];
    };

    # ── THE INTERPRETER ──
    test-ground-fires = {
      expr = strip (fire tuckBody { thimble = "x"; } { });
      expected = [
        {
          ctor = "member";
          kind = "tuck";
          payload.description = "tuck-x";
        }
      ];
    };
    # P3: under D an absent coordinate is FALSE, read from the admitted body (one D by construction).
    test-one-D-absent-is-false = {
      expr = strip (fire tuckBody { } { });
      expected = [ ];
    };
    test-open-world-absent-refuses = {
      expr = strip (fire (bodyOf null [ tuck ]) { } { });
      expected = "policy-body/absent-coordinate";
    };
    # P9: a body record with no `declared` is refused by name, never resolved under a silent open world.
    test-a-body-without-declared-is-refused-at-firing = {
      expr =
        let
          r = gp.groundInstances { } { } {
            refused = false;
            opaque = false;
            name = "hand-rolled";
            clauses = [ (builtins.head tuckBody.clauses) ];
          };
        in
        {
          inherit (r) code witness;
        };
      expected = {
        code = "policy-body/skeleton-malformed";
        witness = [ "declared" ];
      };
    };

    # ── THE DOOR CLAUSE (UC1, G5) ──
    test-ref-position-refused = {
      expr = code (
        bodyOf null [
          {
            ctor = "member";
            kind = "k";
            payload.a = t.ref rDoor;
          }
        ]
      );
      expected = "policy-body/ref-position";
    };
    test-door-whole-body-admitted = {
      expr = code hostBody;
      expected = "admitted";
    };
    test-door-fires-nested-scope = {
      expr = strip (gp.groundInstances { door = stubDoor; } { host = "h"; } hostBody);
      expected = [
        {
          ctor = "suppress";
          target = "captured:CLOSURE-MARKER";
        }
        {
          ctor = "member";
          kind = "host";
          payload.host = "h";
        }
      ];
    };
    test-door-not-fired-when-absent = {
      expr = strip (gp.groundInstances { door = stubDoor; } { } hostBody);
      expected = [ ];
    };
    # P7: a nested door clause from the door's output passes the same walk as a written one, under
    # the body's D, before it fires.
    test-a-nested-door-clause-is-checked-before-it-fires = {
      expr =
        map
          (
            nested:
            (gp.groundInstances { door = doorAnswering nested; } { host = "h"; } hostBody).code or "fired"
          )
          [
            (doorClause // { body = t.lit 1; })
            (doorClause // { when = t.has "hots"; })
          ];
      expected = [
        "policy-body/door-clause-body"
        "policy-body/undeclared-name"
      ];
    };
    # The per-firing check, published: the one row table the gen-rules door reads. The escape that
    # once applied it is retired (U3r), and its firing alias names this check.
    test-codomain-breaches-is-the-per-firing-check = {
      expr =
        let
          contract = {
            emits = [ "host" ];
            binds = [ "host" ];
            suppresses = [ ];
          };
          ds = [
            {
              ctor = "member";
              kind = "host";
              payload = {
                host = 1;
                extra = 2;
              };
            }
            {
              ctor = "suppress";
              target = "p";
            }
            { modules = [ ]; }
          ];
        in
        [
          (gp.codomainBreaches contract ds)
          (
            let
              r = gp.fireEscape (contract // { fn = _: [ (builtins.head ds) ]; }) { };
            in
            r.code == "policy-body/escape-retired" && builtins.match ".*`codomainBreaches`.*" r.message != null
          )
        ];
      expected = [
        [
          {
            field = "binds";
            delta = "extra";
          }
          {
            field = "suppresses";
            delta = "p";
          }
          {
            field = "shape";
            delta = "a declaration without a ctor";
          }
        ]
        true
      ];
    };
    # A `null` field is the over-approximation a door clause may declare: it admits every name, never
    # aborts; the finite field beside it still reports its breach.
    test-codomain-breaches-null-admits-all = {
      expr =
        let
          ds = [
            {
              ctor = "member";
              kind = "host";
              payload.extra = 1;
            }
            {
              ctor = "suppress";
              target = "p";
            }
          ];
        in
        [
          (gp.codomainBreaches {
            emits = [ "host" ];
            binds = null;
            suppresses = [ "p" ];
          } ds)
          (gp.codomainBreaches {
            emits = [ "host" ];
            binds = [ "extra" ];
            suppresses = null;
          } ds)
          (gp.codomainBreaches {
            emits = [ "host" ];
            binds = null;
            suppresses = [ ];
          } ds)
        ];
      expected = [
        [ ]
        [ ]
        [
          {
            field = "suppresses";
            delta = "p";
          }
        ]
      ];
    };
    test-codomain-over-approx = {
      expr = gp.deriveCodomain hostBody;
      expected = {
        emits = [ "host" ];
        binds = null;
        suppresses = [ ];
      };
    };

    # ── THE LITERAL TIER (fuci G1) ──
    test-when-literal-lowers = {
      expr =
        let
          d = decl {
            head = "yoke:bolt";
            when = t.all [
              (t.has "a")
              (t.not (t.has "b"))
            ];
          };
        in
        {
          inherit (d) pos neg;
        };
      expected = {
        pos = [ "a" ];
        neg = [ "b" ];
      };
    };
    test-when-solves-as-pos-neg = {
      expr = [
        (ans (
          modelOf (c105 {
            neg = [ "gusset-held:bolt" ];
          })
        ))
        (ans (
          modelOf (c105 {
            when = t.not (t.has "gusset-held:bolt");
          })
        ))
      ];
      expected = [
        [
          false
          true
        ]
        [
          false
          true
        ]
      ];
    };
    test-absent-atom-false = {
      expr = ans (
        modelOf (c105 {
          when = t.has "never-derived:bolt";
        })
      );
      expected = [
        false
        true
      ];
    };
    test-when-any-refused = {
      expr = refusesCatchably (decl {
        head = "h";
        when = t.any [
          (t.has "a")
          (t.has "b")
        ];
      });
      expected = true;
    };
    test-when-eq-refused = {
      expr = refusesCatchably (decl {
        head = "h";
        when = t.eq [ "a" ] 1;
      });
      expected = true;
    };
    test-when-function-refused = {
      expr = refusesCatchably (decl {
        head = "h";
        when = _: true;
      });
      expected = true;
    };

    # ── IDENTITY (ADR-0034; R9) ──
    test-rule-identity = {
      expr =
        let
          a = ruleMintOf tuckBody;
          b = ruleMintOf (bodyOf D [ (tuck // { payload.description = t.lit "other"; }) ]);
          a2 = ruleMintOf (bodyOf D [ tuck ]);
        in
        [
          (a != null)
          (a == a2)
          (a != b)
        ];
      expected = [
        true
        true
        true
      ];
    };
    test-firing-identity-by-source = {
      expr =
        let
          m = ctx: s: minted (builtins.head (fire tuckBody ctx { thimble = s; }));
        in
        [
          (m { thimble = "x"; } (src "1") == m { thimble = "y"; } (src "1"))
          (m { thimble = "x"; } (src "1") != m { thimble = "x"; } (src "2"))
        ];
      expected = [
        true
        true
      ];
    };
    # C1: under D an absent coordinate is a two-valued fact, so the firing of a negated safeguard
    # mints — over the fixed absence tag — and still keys on the sources of what is present.
    test-firing-identity-safeguard = {
      expr =
        let
          guarded = bodyOf D [
            (
              tuck
              // {
                when = t.all [
                  (t.has "thimble")
                  (t.not (t.has "bobbin"))
                ];
              }
            )
          ];
          bare = bodyOf D [
            {
              ctor = "suppress";
              when = t.not (t.has "bobbin");
              target = "p";
            }
          ];
          m = b: s: minted (builtins.head (fire b { thimble = "x"; } { thimble = s; }));
        in
        [
          (m guarded (src "1") != null)
          (m bare (src "1") != null)
          (m guarded (src "1") != m guarded (src "2"))
        ];
      expected = [
        true
        true
        true
      ];
    };
    test-firing-identity-any-partial = {
      expr =
        let
          b = bodyOf D [
            {
              ctor = "suppress";
              when = t.any [
                (t.has "thimble")
                (t.has "bobbin")
              ];
              target = "p";
            }
          ];
          partial = minted (builtins.head (fire b { thimble = "x"; } { thimble = src "1"; }));
          whole = minted (
            builtins.head (
              fire b
                {
                  thimble = "x";
                  bobbin = "y";
                }
                {
                  thimble = src "1";
                  bobbin = src "2";
                }
            )
          );
        in
        [
          (partial != null)
          (whole != null)
          (partial != whole)
        ];
      expected = [
        true
        true
        true
      ];
    };
    # OQ-H: an iteration item's source is the iteration's own — its rule identity, the sources of
    # `over`'s reads and the item's position.
    test-firing-identity-forEach-item = {
      expr =
        let
          ids =
            s:
            map minted (
              fire environments {
                environments = [
                  "prod"
                  "dev"
                ];
              } { environments = s; }
            );
          one = ids (src "1");
        in
        [
          (!(builtins.elem null one))
          (builtins.elemAt one 0 != builtins.elemAt one 1)
          (one != ids (src "2"))
        ];
      expected = [
        true
        true
        true
      ];
    };

    # ── THE ITERATION ──
    test-forEach-over-term = {
      expr = [
        (strip (
          fire environments {
            environments = [
              "prod"
              "dev"
            ];
          } { }
        ))
        (strip (fire environments { } { }))
      ];
      expected = [
        [
          {
            ctor = "member";
            kind = "environment";
            payload.environment = "prod";
          }
          {
            ctor = "member";
            kind = "environment";
            payload.environment = "dev";
          }
        ]
        [ ]
      ];
    };
    # C2: `over`'s cover is its safety reads, so a `has` test inside it stays a test and the
    # iteration fires as the core resolves `over`.
    test-forEach-over-test-not-guard = {
      expr =
        let
          b =
            bodyOf
              [ "environments" "extra" ]
              [
                {
                  over = t.ifThenElse (t.has "extra") (t.lit [
                    "x"
                    "y"
                  ]) (t.lit [ "fallback" ]);
                  emit = [
                    {
                      ctor = "member";
                      kind = "e";
                      payload.e = t.readCtx "item" [ ];
                    }
                  ];
                }
              ];
          es = ctx: map (d: d.payload.e) (fire b ctx { });
        in
        [
          (es { environments = [ ]; })
          (es {
            environments = [ ];
            extra = 1;
          })
        ];
      expected = [
        [ "fallback" ]
        [
          "x"
          "y"
        ]
      ];
    };

    # ── CONFLUENCE (ADR-0022) ──
    test-confluence-literal-order = {
      expr =
        let
          rulesOf =
            w:
            (gp.program
              [ "bolt" ]
              [
                {
                  head = "h:bolt";
                  relata = [ "bolt" ];
                  when = w;
                }
              ]
            ).rules;
          canon = map (
            r:
            r
            // {
              pos = builtins.sort (a: b: a < b) r.pos;
              neg = builtins.sort (a: b: a < b) r.neg;
            }
          );
        in
        canon (
          rulesOf (
            t.all [
              (t.has "a")
              (t.has "c")
              (t.not (t.has "b"))
            ]
          )
        ) == canon (
          rulesOf (
            t.all [
              (t.not (t.has "b"))
              (t.has "c")
              (t.has "a")
            ]
          )
        );
      expected = true;
    };
    # P4: the fired list's ORDER is not contract — the set is. Compared in canonical order, with the
    # length pinned so an empty firing cannot pass.
    test-confluence-clause-order = {
      expr =
        let
          s1 = {
            ctor = "suppress";
            when = t.has "thimble";
            target = "p";
          };
          fired =
            cs:
            builtins.sort (a: b: a < b) (
              map builtins.toJSON (strip (fire (bodyOf D cs) { thimble = "x"; } { }))
            );
        in
        {
          equal =
            fired [
              tuck
              s1
            ] == fired [
              s1
              tuck
            ];
          length = builtins.length (fired [
            tuck
            s1
          ]);
        };
      expected = {
        equal = true;
        length = 2;
      };
    };

    # ── U3r: THE ESCAPE'S RETIREMENT (spec §2.10) ──
    # `escape` and `fireEscape` stay published with their original arity and refuse BY NAME, as a
    # tagged value, naming the door; whatever they are handed — the old five-field form, or one with
    # an unknown field — gets the same answer. The green twin is the door's own path: a door clause
    # admitted through `body` in the same run.
    test-escape-retired = {
      expr =
        let
          old = gp.escape {
            name = "e";
            fn = _: [ ];
            emits = [ ];
            binds = [ ];
            suppresses = [ ];
          };
        in
        {
          escape = code old;
          unknownField = code (
            gp.escape {
              name = "e";
              fn = _: [ ];
              emits = [ ];
              binds = [ ];
              suppresses = [ ];
              unknown = 1;
            }
          );
          fireEscape = code (gp.fireEscape old { });
          tryEval = (builtins.tryEval (builtins.deepSeq old null)).success;
          inherit (old) witness message;
          door = code hostBody;
        };
      expected = {
        escape = "policy-body/escape-retired";
        unknownField = "policy-body/escape-retired";
        fireEscape = "policy-body/escape-retired";
        tryEval = true;
        witness.retired = "escape";
        message = "`escape` is retired: gen-program's algebra is terms only, and the only closure crossing in gen is the gen-rules door. write the slot as a term of gen-algebra's `term` algebra, or, for a closure, cross the gen-rules door: its lowering (`defunctionalize`) registers the closure and hands gen-program a door clause whose body is `ref r`, which `groundInstances` resolves through the door (`mkApply`); the per-firing codomain check is `codomainBreaches`, applied by the door";
        door = "admitted";
      };
    };
    # `admit` refuses an escape record by name whichever marker it carries, and `deriveCodomain` does
    # the same when one is handed to it directly — never the old declared-contract read.
    test-admit-escape-record-refused = {
      expr =
        let
          rec0 = {
            name = "e";
            fn = _: [ ];
            emits = [ ];
            binds = [ ];
            suppresses = [ ];
          };
        in
        {
          both = code (
            gp.admit (
              rec0
              // {
                refused = false;
                __isPolicy = true;
                opaque = true;
              }
            )
          );
          opaqueOnly = code (gp.admit (rec0 // { opaque = true; }));
          isPolicyOnly = code (gp.admit (rec0 // { __isPolicy = true; }));
          missingField = code (
            gp.admit {
              opaque = true;
              name = "e";
            }
          );
          deriveCodomain = code (
            gp.deriveCodomain (
              rec0
              // {
                refused = false;
                opaque = true;
              }
            )
          );
          deriveCodomainIsPolicy = code (gp.deriveCodomain (rec0 // { __isPolicy = true; }));
          control = code (
            gp.admit {
              name = "nf";
              clauses = [ ];
              declared = null;
            }
          );
        };
      expected = {
        both = "policy-body/escape-retired";
        opaqueOnly = "policy-body/escape-retired";
        isPolicyOnly = "policy-body/escape-retired";
        missingField = "policy-body/escape-retired";
        deriveCodomain = "policy-body/escape-retired";
        deriveCodomainIsPolicy = "policy-body/escape-retired";
        control = "admitted";
      };
    };
  };
}
