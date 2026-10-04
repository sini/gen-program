# THE SOLVED MODEL'S EDGES — the answering half. The refusals are message cells in
# `ci/tests-error.nix`; these are what `ruleEdges` answers.
#
# ★ EVERY FIXTURE SOLVES FROM THE LABELLED DECLARATIONS THEMSELVES, handed to `program` unstripped,
# so each cell exercises the door that admits `label` as well as the export that reads it.
{
  genProgram,
  scope,
  identity,
  ...
}:
let
  solve =
    {
      declarations,
      frozen,
      complete ? true,
      prior ? null,
    }:
    genProgram.model {
      program = genProgram.program frozen declarations;
      interpretation = [ ];
      inherit complete prior;
    };

  edgesOf = args: genProgram.ruleEdges (solve args) args.declarations;

  # A conditional edge and an unlabelled conditional promotion over the same guard: the edge holds
  # while `snag:loom` is not derived.
  weave = [
    {
      head = "warp:loom";
      relata = [ "loom" ];
    }
    {
      head = "shed:heddle:reed";
      pos = [ "warp:loom" ];
      neg = [ "snag:loom" ];
      relata = [
        "heddle"
        "reed"
      ];
      label = "shed";
    }
    {
      head = "pick:loom:heddle";
      pos = [ "warp:loom" ];
      neg = [ "snag:loom" ];
      relata = [
        "loom"
        "heddle"
      ];
    }
  ];
  weaveFrozen = [
    "loom"
    "heddle"
    "reed"
  ];
  shedEdge = {
    from = "heddle";
    to = "reed";
    label = "shed";
  };

  on = edgesOf {
    declarations = weave;
    frozen = weaveFrozen;
  };
  # The OFF plant: the guard's negated membership becomes a fact, so the edge resolves off.
  off = edgesOf {
    declarations = weave ++ [
      {
        head = "snag:loom";
        relata = [ "loom" ];
      }
    ];
    frozen = weaveFrozen;
  };

  noModel = genProgram.ruleEdges (throw "no model was asked for") weave;

  # ── THE PROMOTED HEAD: a node over THREE labelled relata, under the weave's own guard ──
  # Edge or node is declared on the rule, never read off the relata count, so the fixture is n = 3
  # beside the corpus's n = 2 (gen-demo C5).
  tieHead = "tie:loom:heddle:reed";
  tieRelata = {
    warp = "loom";
    harness = "heddle";
    beater = "reed";
  };
  tie = {
    head = tieHead;
    pos = [ "warp:loom" ];
    neg = [ "snag:loom" ];
    relata = tieRelata;
    promote = "tie";
  };
  tieRecord = {
    identifier = tieHead;
    kind = "tie";
    relata = tieRelata;
    content = { };
    site = "gen-program.ruleEdges:${tieHead}";
  };
  # The mint's own edge rule: head -> relatum, labelled by role, in label order.
  tieEdges = [
    {
      from = tieHead;
      to = "reed";
      label = "beater";
    }
    {
      from = tieHead;
      to = "heddle";
      label = "harness";
    }
    {
      from = tieHead;
      to = "loom";
      label = "warp";
    }
  ];
  tieOn = edgesOf {
    declarations = weave ++ [ tie ];
    frozen = weaveFrozen;
  };
  tieOff = edgesOf {
    declarations = weave ++ [
      tie
      {
        head = "snag:loom";
        relata = [ "loom" ];
      }
    ];
    frozen = weaveFrozen;
  };
  tieNoModel = genProgram.ruleEdges (throw "no model was asked for") (weave ++ [ tie ]);

  # ── THE CALLER MINTS: the relata's emitters and the promoted records, one mint, pass 1 ──
  entity = identifier: kind: {
    pass = 0;
    inherit identifier kind;
    relata = { };
    content = { };
    site = "ci:${identifier}";
  };
  relataEmitters = [
    (entity "loom" "frame")
    (entity "heddle" "eye")
    (entity "reed" "comb")
  ];
  minted = scope.mintStrata { } (relataEmitters ++ map (p: p // { pass = 1; }) tieOn.promoted);
  idOf = n: minted.nodes.${n}.identity;
  labels = builtins.attrNames tieRelata;
  # ADR-0016 rulings 4 and 5: the identity keys are the relatum labels plus the node's own
  # identifier, and each relatum's VALUE is its minted identity.
  expectedIdentity = identity.hashIdentity "tie" ([ "identifier" ] ++ labels) (
    l: if l == "identifier" then tieHead else idOf tieRelata.${l}
  );
  # The discriminating arm: the same hash over the relata's IDENTIFIERS, the constructed identity
  # this construction exists to refuse.
  constructedIdentity = identity.hashIdentity "tie" ([ "identifier" ] ++ labels) (
    l: if l == "identifier" then tieHead else tieRelata.${l}
  );
  forces = v: (builtins.tryEval (builtins.deepSeq v true)).success;

  ab = [
    "a"
    "b"
  ];
  passOne = [
    {
      head = "r:a:b";
      relata = ab;
      label = "r";
    }
  ];
  passTwo = passOne ++ [
    {
      head = "r:b:c";
      pos = [ "r:a:b" ];
      relata = [
        "b"
        "c"
      ];
      label = "r";
    }
  ];
  staged = edgesOf {
    declarations = passTwo;
    frozen = [
      "a"
      "b"
      "c"
    ];
    prior = solve {
      declarations = passOne;
      frozen = ab;
      complete = false;
    };
  };
in
{
  flake.tests.ruleEdges = {
    test-reached-is-the-included-labelled-edge = {
      expr = on.reached;
      expected = [ shedEdge ];
    };
    test-candidates-hold-every-labelled-edge = {
      expr = on.candidates;
      expected = [ shedEdge ];
    };

    # What separates an export that reads the verdict from one that ignores it.
    test-an-edge-resolved-off-is-absent-from-reached = {
      expr = off.reached;
      expected = [ ];
    };
    test-an-edge-resolved-off-stays-a-candidate = {
      expr = off.candidates;
      expected = [ shedEdge ];
    };

    # `candidates` is the declared edge set, complete at registration, and never forces the model.
    # The same throw under `reached` is the arm that shows the probe can fail.
    test-candidates-never-force-the-model = {
      expr = forces noModel.candidates;
      expected = true;
    };
    test-control-reached-forces-the-model = {
      expr = forces noModel.reached;
      expected = false;
    };

    # An explicit `null` is the omission: no candidate and no reached edge.
    test-an-explicit-null-label-is-no-edge = {
      expr = edgesOf {
        declarations = [
          {
            head = "r:a:b";
            relata = ab;
            label = null;
          }
        ];
        frozen = ab;
      };
      expected = {
        candidates = [ ];
        reached = [ ];
        promotions = [ ];
        promoted = [ ];
      };
    };

    # Keyed by head: two rules for one membership naming one edge are one edge, never two.
    test-agreeing-declarations-of-one-head-collapse = {
      expr = edgesOf {
        declarations = [
          {
            head = "r:a:b";
            relata = ab;
            label = "r";
          }
          {
            head = "r:a:b";
            pos = [ "f" ];
            relata = ab;
            label = "r";
          }
          {
            head = "f";
            relata = [ ];
          }
        ];
        frozen = ab;
      };
      expected = {
        candidates = [
          {
            from = "a";
            to = "b";
            label = "r";
          }
        ];
        reached = [
          {
            from = "a";
            to = "b";
            label = "r";
          }
        ];
        promotions = [ ];
        promoted = [ ];
      };
    };

    # A mid-sequence pass refuses (message cell); the pass that closes the relation, handed the
    # cumulative declarations, returns the earlier pass's edge beside its own.
    test-the-closing-pass-returns-every-pass-edge = {
      expr = staged.reached;
      expected = [
        {
          from = "a";
          to = "b";
          label = "r";
        }
        {
          from = "b";
          to = "c";
          label = "r";
        }
      ];
    };

    # ── PROMOTION (den-hoag-2quxu) ──
    # Binary control: promote-free input publishes no promotion, so `candidates` and `reached` above
    # are the whole answer.
    test-promote-free-input-promotes-nothing = {
      expr =
        map
          (r: [
            r.promotions
            r.promoted
          ])
          [
            on
            off
            staged
          ];
      expected = builtins.genList (_: [
        [ ]
        [ ]
      ]) 3;
    };
    # A promotion record is the mint's emitter minus `pass`, and it carries NO identity: a promotion
    # record is not a node. Model-free, as `candidates` is.
    test-promotions-are-the-records-and-never-force-the-model = {
      expr = builtins.deepSeq tieNoModel.promotions tieNoModel.promotions;
      expected = [ tieRecord ];
    };
    test-a-promotion-record-carries-no-identity = {
      expr = map builtins.attrNames tieNoModel.promotions;
      expected = [
        [
          "content"
          "identifier"
          "kind"
          "relata"
          "site"
        ]
      ];
    };
    test-promoted-is-the-included-promotion = {
      expr = tieOn.promoted;
      expected = [ tieRecord ];
    };
    # What separates an export that reads the verdict from one that ignores it.
    test-a-promotion-resolved-off-is-absent-from-promoted = {
      expr = tieOff.promoted;
      expected = [ ];
    };
    test-a-promotion-resolved-off-stays-a-promotion = {
      expr = tieOff.promotions;
      expected = [ tieRecord ];
    };
    # `candidates` is the declared edge set: the promotion's incident edges beside the labelled edge,
    # whatever the head resolves to. `reached` keeps the labelled edge only; the node's edges are the
    # mint's.
    test-candidates-hold-the-promotion-incident-edges = {
      expr = [
        tieOn.candidates
        tieOff.candidates
        tieNoModel.candidates
      ];
      expected = builtins.genList (_: [ shedEdge ] ++ tieEdges) 3;
    };
    test-reached-holds-no-promotion-edge = {
      expr = tieOn.reached;
      expected = [ shedEdge ];
    };
    # The node is the mint's: its identity is `hashIdentity` over the relata's MINTED identities,
    # and its incident edges are exactly the head's candidate edges.
    test-the-minted-promotion-has-the-mint-identity = {
      expr = minted.nodes.${tieHead}.identity;
      expected = expectedIdentity;
    };
    test-control-an-identity-over-identifiers-differs = {
      expr = constructedIdentity == expectedIdentity;
      expected = false;
    };
    test-the-minted-promotion-edges-are-its-candidate-edges = {
      expr = builtins.filter (e: e.from == tieHead) minted.edges;
      expected = tieEdges;
    };

    test-no-labelled-declaration-reads-no-edge-at-a-growing-relation = {
      expr =
        (edgesOf {
          declarations = [
            {
              head = "r:a:b";
              relata = ab;
            }
          ];
          frozen = ab;
          complete = false;
        }).reached;
      expected = [ ];
    };
  };
}
