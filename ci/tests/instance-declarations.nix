# THE BRIDGE, ASSERTED (`instanceDeclarations`): fired policy bodies lowered to declarations and
# solved by the well-founded engine. Every expected value below is an answer read off the solved
# model (`T` included, `F` excluded, `U` undefined) or a count, never a re-statement of the
# construction.
#
# The planted violations each cell is read against (a mutated bridge) are measured at the landing
# and recorded with it; the controls that need no mutated library live here, beside their cell: the
# G10 fingerprint is shown to read declaration ORDER (a reversed list moves it), and G13's bridged
# fact is read beside its hand-written twin.
#
# Messages (which refusal fired) are on the error plane, `ci/tests-error.nix`.
{
  genProgram,
  prelude,
  algebra,
  T,
  ...
}:
let
  fx = import ./_fixtures/instance-declarations.nix { inherit prelude genProgram T; };
  inherit (fx)
    B
    gp
    local
    at
    verdicts
    pf
    pfb
    hf
    ;
  inherit (T.term) has;
  refuses = e: !(builtins.tryEval (builtins.deepSeq e true)).success;

  # A permutation fingerprint: the solved rule set, the firing identities, their heads, AND the
  # declarations in the order the bridge emits them (head and guard identity).
  fingerprint =
    r:
    builtins.toJSON {
      rules = builtins.attrNames (fx.solve r.declarations).rules;
      firings = builtins.attrNames r.firings;
      heads = map (f: f.head) (builtins.attrValues r.firings);
      declarations = map (d: [
        d.head
        (algebra.identityOf d.when).minted
      ]) r.declarations;
    };
  idMap =
    r:
    builtins.toJSON (
      builtins.mapAttrs (_: f: {
        inherit (f) head;
        c = fx.content f;
      }) r.firings
    );
  ordersOf = n: fx.perms (builtins.genList (builtins.elemAt fx.permApps) n);

  five = B fx.fiveNames [ (at "bolt:a" fx.weave) ];
  fiveDecls = fx.facts ++ five.declarations;
  fiveModel = gp.model {
    program = gp.program [ "bolt:a" "overlock" ] fiveDecls;
    interpretation = [ ];
    complete = true;
    prior = null;
  };

  staged = fx.solveWith false [ ];
  bridgedStaged = staged (B local [ (at "bolt:a" fx.pleat) ]).declarations;
  twinStaged = staged [
    {
      head = pf;
      relata = [ ];
      when = has "bolt:a";
    }
  ];
in
{
  flake.tests.instance-declarations = {
    # ── LIVE CONTROL: the export is published and lowers a lone firing ──
    test-control-a-lone-firing-holds = {
      expr = (verdicts local [ (at "bolt:a" fx.pleat) ] [ pf ]).${pf};
      expected = "T";
    };

    # G1 · a fired suppression defeats its target's firing at the context.
    test-g1-a-fired-suppression-defeats = {
      expr = (verdicts local [ (at "bolt:a" fx.pleat) (at "bolt:a" fx.hem) ] [ pf ]).${pf};
      expected = "F";
    };

    # G2 · a suppression is itself defeasible: baste-cutter ⊣ hem ⊣ pleat leaves pleat holding.
    test-g2-a-chain-leaves-the-first-target-holding = {
      expr =
        verdicts local
          [ (at "bolt:a" fx.pleat) (at "bolt:a" fx.hem) (at "bolt:a" fx.hemCutter) ]
          [
            pf
            "ab:pleat@bolt:a"
            "ab:hem@bolt:a"
          ];
      expected = {
        ${pf} = "T";
        "ab:hem@bolt:a" = "T";
        "ab:pleat@bolt:a" = "F";
        adjudication = "admitted";
      };
    };

    # G3 · an even cycle takes the well-founded outcome: every contested atom undefined, two stable
    # models, admitted.
    test-g3-an-even-cycle-is-undefined-and-admitted = {
      expr =
        verdicts local
          [ (at "bolt:a" fx.pleatC) (at "bolt:a" fx.hemC) ]
          [
            pf
            hf
            "ab:pleat@bolt:a"
            "ab:hem@bolt:a"
          ];
      expected = {
        ${pf} = "U";
        ${hf} = "U";
        "ab:pleat@bolt:a" = "U";
        "ab:hem@bolt:a" = "U";
        adjudication = "admitted";
      };
    };

    # G4 · a self-suppression has no stable model: undefined, and the coherence fact says refused.
    test-g4-an-odd-cycle-is-undefined-and-refused = {
      expr =
        verdicts local
          [ (at "bolt:a" fx.selfish) ]
          [
            pf
            "ab:pleat@bolt:a"
          ];
      expected = {
        ${pf} = "U";
        "ab:pleat@bolt:a" = "U";
        adjudication = "refused";
      };
    };

    # G5 · a declared codomain is not a fired suppression: hem's guarded suppress names pleat in its
    # codomain, fires nothing at a context without `lint`, and pleat holds.
    test-g5-a-declared-codomain-suppresses-nothing = {
      expr = {
        codomain = (gp.deriveCodomain fx.hemGuarded).suppresses;
        fired = builtins.length (gp.groundInstances { sources.spool = "spool:a"; } fx.ctx fx.hemGuarded);
        verdict = (verdicts local [ (at "bolt:a" fx.pleat) (at "bolt:a" fx.hemGuarded) ] [ pf ]).${pf};
      };
      expected = {
        codomain = [ "pleat" ];
        fired = 0;
        verdict = "T";
      };
    };

    # G6 · multiple contexts are the caller's naming: an `at`-keyed abnormality is context-local, a
    # policy-keyed one is program-global.
    test-g6-suppression-scope-is-the-namers = {
      expr =
        let
          apps = [
            (at "bolt:a" fx.pleat)
            (at "bolt:b" fx.pleat)
            (at "bolt:a" fx.hem)
          ];
        in
        {
          local = verdicts local apps [
            pf
            pfb
          ];
          global =
            verdicts
              {
                fact = fx.factByContent;
                abnormal = fx.abGlobal;
              }
              apps
              [
                pf
                pfb
              ];
        };
      expected = {
        local = {
          ${pf} = "F";
          ${pfb} = "T";
          adjudication = "admitted";
        };
        global = {
          ${pf} = "F";
          ${pfb} = "F";
          adjudication = "admitted";
        };
      };
    };

    # G7 · firing identity across contexts: a read-free body's firing mints equal at two contexts,
    # and the bridge keeps the two firings and their two declarations apart.
    test-g7-firing-identity-carries-the-context = {
      expr =
        let
          r = B local [
            (at "bolt:a" fx.tack)
            (at "bolt:b" fx.tack)
          ];
        in
        {
          rawEqual = fx.rawMints fx.tack "bolt:a" == fx.rawMints fx.tack "bolt:b";
          firings = builtins.length (builtins.attrNames r.firings);
          declarations = builtins.length r.declarations;
        };
      expected = {
        rawEqual = true;
        firings = 2;
        declarations = 2;
      };
    };

    # G8 · the producer's rule identity carries the constructor and the kind: a member and a
    # deliver with one condition and payload, and two kinds of member, mint apart in
    # `groundInstances` itself, and the bridge keeps two firings of each.
    test-g8-the-rule-identity-carries-constructor-and-kind = {
      expr =
        let
          pair = ms: builtins.elemAt ms 0 == builtins.elemAt ms 1;
          firingsOf =
            b:
            builtins.length (
              builtins.attrNames
                (B {
                  fact = fx.factByPolicy;
                  abnormal = fx.abLocal;
                } [ (at "bolt:a" b) ]).firings
            );
        in
        {
          ctorRawEqual = pair (fx.rawMints fx.seam "bolt:a");
          kindRawEqual = pair (fx.rawMints fx.twoKinds "bolt:a");
          ctorFirings = firingsOf fx.seam;
        };
      expected = {
        ctorRawEqual = false;
        kindRawEqual = false;
        ctorFirings = 2;
      };
    };

    # G9 · two policies naming one fact are two supports of it, so suppressing either leaves it.
    test-g9-two-supports-of-one-fact = {
      expr = {
        supports = builtins.length (
          builtins.filter (f: f.head == pf) (
            builtins.attrValues
              (B local [
                (at "bolt:a" fx.pleat)
                (at "bolt:a" fx.baste)
              ]).firings
          )
        );
        pleatSuppressed =
          (verdicts local [ (at "bolt:a" fx.pleat) (at "bolt:a" fx.baste) (at "bolt:a" fx.hem) ] [ pf ])
          .${pf};
        basteSuppressed =
          (verdicts local [ (at "bolt:a" fx.pleat) (at "bolt:a" fx.baste) (at "bolt:a" fx.snip) ] [ pf ])
          .${pf};
      };
      expected = {
        supports = 2;
        pleatSuppressed = "T";
        basteSuppressed = "T";
      };
    };

    # G10 · no position is an identity: every order of 2, 3 and 4 applications gives one fingerprint
    # (declarations in emitted order included) and one verdict set; two clause orders give one
    # id-map.
    test-g10-application-order-moves-nothing = {
      expr =
        map
          (n: {
            orders = builtins.length (ordersOf n);
            fingerprints = fx.distinct (map (p: fingerprint (B local p)) (ordersOf n));
          })
          [
            2
            3
            4
          ];
      expected = [
        {
          orders = 2;
          fingerprints = 1;
        }
        {
          orders = 6;
          fingerprints = 1;
        }
        {
          orders = 24;
          fingerprints = 1;
        }
      ];
    };
    test-g10-verdicts-and-clause-order = {
      expr = {
        verdicts = fx.distinct (
          map (
            p:
            builtins.toJSON (
              verdicts local p [
                pf
                pfb
                "ab:pleat@bolt:a"
                "ab:hem@bolt:a"
              ]
            )
          ) (ordersOf 4)
        );
        clauseOrders = fx.distinct (
          map (o: idMap (B local [ (at "bolt:a" (fx.twoClause o)) ])) [
            true
            false
          ]
        );
      };
      expected = {
        verdicts = 1;
        clauseOrders = 1;
      };
    };
    # The fingerprint's control: it reads the emitted order, so a reordered declaration list moves it.
    test-g10-control-the-fingerprint-reads-declaration-order = {
      expr =
        let
          r = B local fx.permApps;
        in
        fingerprint r == fingerprint (r // { declarations = prelude.reverseList r.declarations; });
      expected = false;
    };

    # G11 · activation is not completion: a deliver whose payload throws if read solves to T.
    test-g11-activation-does-not-read-the-content = {
      expr = fx.read (fx.solve
        (B {
          fact = fx.factByPolicy;
          abnormal = fx.abLocal;
        } [ fx.sentinelApp ]).declarations
      ) "deliver:bundle@bolt:a";
      expected = "T";
    };

    # G12 · total over the five constructors; the edge reaches the model's edges with its label.
    test-g12-every-constructor-lowers = {
      expr = {
        ctors = builtins.sort (a: b: a < b) (map (f: f.ctor) (builtins.attrValues five.firings));
        heads = builtins.sort (a: b: a < b) (map (d: d.head) five.declarations);
        reached = (gp.ruleEdges fiveModel fiveDecls).reached;
      };
      expected = {
        ctors = [
          "deliver"
          "edge"
          "member"
          "realize"
          "suppress"
        ];
        heads = [
          "ab:hem@bolt:a"
          "deliver:weave@bolt:a"
          "edge:bolt:a>overlock"
          "member:weave@bolt:a"
          "realize:weave@bolt:a"
        ];
        reached = [
          {
            from = "bolt:a";
            label = "stitch";
            to = "overlock";
          }
        ];
      };
    };

    # G13 · every bridged fact rests on negation, so under a growing relation it is withheld; the
    # same fact written by hand with no defeat literal answers.
    test-g13-a-bridged-fact-is-withheld-while-growing = {
      expr = {
        bridgedFlag = (bridgedStaged.resolve pf).flag;
        withheld = bridgedStaged.withheldAtoms;
        twin = twinStaged.resolve pf;
      };
      expected = {
        bridgedFlag = "P";
        withheld = [ pf ];
        twin = {
          flag = "P";
          included = true;
        };
      };
    };

    # The refusals, as booleans (their messages are on the error plane).
    test-every-collision-is-refused = {
      expr = map refuses [
        (B local [
          (at "bolt:a" fx.pleat)
          (at "bolt:a" fx.pleat)
        ]).declarations
        (B fx.factAsAb [
          (at "bolt:a" fx.pleat)
          (at "bolt:a" fx.hem)
        ]).declarations
        (B fx.ctorBlind [ (at "bolt:a" fx.memberAndDeliver) ]).declarations
        (B local [
          (at "bolt:a" fx.pleat)
          (at "bolt:b" fx.otherPleat)
        ]).declarations
        (B local [ (fx.doorApp fx.twoOut) ]).declarations
        (B local [ fx.unsourced ]).declarations
        (B fx.factWithWhen [ (at "bolt:a" fx.pleat) ]).declarations
        (B fx.abWithLabel [
          (at "bolt:a" fx.pleat)
          (at "bolt:a" fx.hem)
        ]).declarations
      ];
      expected = [
        true
        true
        true
        true
        true
        true
        true
        true
      ];
    };
  };
}
