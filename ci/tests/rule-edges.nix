# THE SOLVED MODEL'S EDGES — the answering half. The refusals are message cells in
# `ci/tests-error.nix`; these are what `ruleEdges` answers.
#
# ★ EVERY FIXTURE SOLVES FROM THE LABELLED DECLARATIONS THEMSELVES, handed to `program` unstripped,
# so each cell exercises the door that admits `label` as well as the export that reads it.
{ genProgram, ... }:
let
  solve =
    {
      declarations,
      frozen,
      complete ? true,
      prior ? null,
    }:
    genProgram.model {
      program = genProgram.program { inherit declarations frozen; };
      interpretation = [ ];
      inherit complete prior;
    };

  edgesOf =
    args:
    genProgram.ruleEdges {
      inherit (args) declarations;
      model = solve args;
    };

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

  noModel = genProgram.ruleEdges {
    declarations = weave;
    model = throw "no model was asked for";
  };
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
