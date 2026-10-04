# THE OPERAND DOORS, VALUE PLANE (den-hoag-l3cwb) — what the operand checks leave ANSWERING. The
# refusals by message are cells in `ci/tests-error.nix`; these are the tagged-value refusals of
# `groundInstances` (its regime is "refusals are tagged values", not throws) and the
# paths the checks keep legal.
{
  genProgram,
  scope,
  ...
}:
let
  body = genProgram.body {
    name = "operand-doors";
    declared = [ ];
    clauses = [ ];
  };
  ground = opts: ctx: genProgram.groundInstances opts ctx body;

  # `ruleEdges` reads its model only when a declaration is labelled, so a caller with no labelled
  # declaration may hand it any model (gen-inspect's subject, gen-demo's C25).
  unlabelled = [
    {
      head = "u";
      relata = [ ];
    }
  ];
  program = genProgram.program [ ] [ ];
  solved = scope.solve [ ] program;
  adjudication = genProgram.adjudicate {
    inherit program;
    model = solved;
    interpretation = [ ];
  };
  whole = genProgram.mkModel {
    inherit solved program adjudication;
    complete = true;
  };
in
{
  flake.tests = {
    # ── G1: the context is a map ──
    test-ground-instances-refuses-a-null-context = {
      expr = with (ground { } null); [
        refused
        code
        witness
      ];
      expected = [
        true
        "policy-body/context-malformed"
        "null"
      ];
    };
    test-ground-instances-refuses-an-int-context = {
      expr = (ground { } 5).witness;
      expected = "int";
    };
    test-ground-instances-refuses-a-list-context = {
      expr = (ground { } [ ]).code;
      expected = "policy-body/context-malformed";
    };
    test-ground-instances-refuses-a-string-context = {
      expr = (ground { } "s").witness;
      expected = "string";
    };
    # ── G2: `sources` is a map ──
    test-ground-instances-refuses-a-null-sources-option = {
      expr = with (ground { sources = null; } { }); [
        code
        witness
      ];
      expected = [
        "policy-body/option-malformed"
        [ "sources" ]
      ];
    };
    test-ground-instances-refuses-a-string-sources-option = {
      expr = (ground { sources = "s"; } { }).witness;
      expected = [ "sources" ];
    };
    # ── G3: `door` is a function or null ──
    test-ground-instances-refuses-an-int-door-option = {
      expr = with (ground { door = 5; } { }); [
        code
        witness
      ];
      expected = [
        "policy-body/option-malformed"
        [ "door" ]
      ];
    };
    # ── controls: the same calls with a well-formed operand answer ──
    test-control-ground-instances-answers-a-well-formed-call = {
      expr = ground {
        sources = { };
        door = null;
      } { };
      expected = [ ];
    };
    # ── V1: the check is on READ, so a degenerate model with nothing labelled stays legal ──
    test-rule-edges-with-nothing-labelled-reads-no-model = {
      expr = (genProgram.ruleEdges 5 unlabelled).reached;
      expected = [ ];
    };
    test-rule-edges-admits-a-gen-scope-shaped-model-with-nothing-labelled = {
      expr =
        (genProgram.ruleEdges {
          trueAtoms = [ ];
          verdict = _: "false";
        } [ ]).reached;
      expected = [ ];
    };
    # ── V2: the control for the element check (the refusals are error cells): a real solve is admitted ──
    test-control-mk-model-admits-a-real-solve = {
      expr = builtins.deepSeq whole whole.complete;
      expected = true;
    };
  };
}
