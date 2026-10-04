# THE SOLVED MODEL'S EDGES: a labelled declaration's head, when included, IS an edge of the graph.
#
# A declaration carrying a `label` asserts that its head denotes `{ from = relata[0]; to =
# relata[1]; label; }` — the record gen-scope's mint emits and the corpus's edge list carries. The
# endpoints are the RELATA, so every one has already passed the frozen-set check in `program`
# (ADR-0016 ruling 7, ADR-0033 clause 1): a same-pass endpoint cannot be written. The label is the
# rule's own and never parsed out of the atom, which is caller text this library does not read.
#
# ── WHY THIS LIVES HERE AND NOT IN gen-scope ──
# gen-scope's model is over opaque atoms and its rules carry no relata: `rule` drops them before
# `mkRule`. The map from a verdict back to the declaration's relation is the declarations→program
# translation run backwards, and that translation is what this library owns (ADR-0008 §1).
#
# ── TWO FIELDS, BOTH PLAIN DATA ──
# · `candidates` — the edge of every labelled declaration, whatever it resolves to. A function of
#   the declarations ALONE: it never forces `model`. That is ADR-0008 §3's declared edge set,
#   complete at registration, and it is what a gate over the policy edges reads.
# · `reached` — the candidates whose head the model includes: ADR-0019's reached projection. An edge
#   that resolves off is absent, indistinguishable from one that never existed. `reached ⊆
#   candidates` by construction: it is a filter of the same keyed set.
# Neither is a graph and neither is a resolver: the caller appends `reached` to its declared edges,
# one edge list, one graph (ADR-0012).
#
# ★ AN EDGE IS A PROPERTY OF THE ATOM, NOT OF THE RULE. A head with several rules is an ordinary
# disjunction, so the labelled set is built KEYED BY HEAD: agreeing claims collapse to one edge and
# conflicting ones refuse by name — gen-scope's mint rule (identical collapses, conflicting refuses)
# applied as the construction, so a duplicate cannot form rather than being filtered out after. The
# conflict is decidable from the declarations, so it refuses in `candidates`, model-free.
#
# ★★ EVERY UNSETTLED ANSWER REFUSES, NAMING EVERY OFFENDING HEAD. An edge list carries no third
# value and no flag, so a set read off a model it cannot represent would collapse the answer:
#   · a head whose flag is `U` — ADR-0020's third value has no edge to be, and dropping it is the
#     silence that clause rules out;
#   · a relation still growing (`complete = false`) — the set asserts a negative for every absent
#     candidate, and the model withholds exactly those until the relation closes. Under
#     `complete = false` no flag is `T`, so this is one read of `model.complete`, not a scan;
#   · a labelled declaration that is not a rule of this model — the model was solved from other
#     declarations and would answer about the wrong program. Keyed by the same canonical-rule index
#     the `prior` omission guard reads.
# One membership's own answer stays available through `model.resolve` in every case.
#
# COST: linear in the labelled declarations — one keyed grouping by head, one rule-index lookup per
# declaration and one `resolve` per head.
{
  prelude,
  declaration,
  ruleKey,
  checkModelRecord,
}:
let
  quoteAll = names: prelude.concatMapStringsSep ", " (n: "'${n}'") names;

  edgeOf = d: {
    from = builtins.elemAt d.relata 0;
    to = builtins.elemAt d.relata 1;
    inherit (d) label;
  };

  # POSITIONAL (den-hoag-7gp66 P2, rule 4): `ruleEdges model declarations`. The declarations are
  # what is read, so they are the subject and go last; the model they are read against is
  # configuration. Positional arity is structural, so the P1 record check retires.
  ruleEdges =
    model: declarations:
    let
      labelled = builtins.filter (d: d.label != null) (map declaration declarations);

      misArity = builtins.filter (d: builtins.length d.relata != 2) labelled;
      byHead = builtins.groupBy (d: d.head) labelled;
      keyed = builtins.mapAttrs (_: ds: edgeOf (builtins.head ds)) byHead;
      conflicting = builtins.filter (h: builtins.any (d: edgeOf d != keyed.${h}) byHead.${h}) (
        builtins.attrNames byHead
      );

      settledKeyed =
        if misArity != [ ] then
          throw "gen-program.ruleEdges: ${
            prelude.concatMapStringsSep ", " (
              d: "'${d.head}' (${toString (builtins.length d.relata)} relata)"
            ) misArity
          } carries a label, but an edge relates exactly two relata, from and to"
        else if conflicting != [ ] then
          throw "gen-program.ruleEdges: ${quoteAll conflicting} is labelled by declarations naming different edges; an edge is a property of the membership, so its declarations must agree on from, to and label"
        else
          keyed;

      candidates = builtins.attrValues settledKeyed;

      unsolved = builtins.filter (d: !(model.rules ? ${ruleKey d})) labelled;
      verdicts = builtins.mapAttrs (h: _: model.resolve h) settledKeyed;
      undefined = builtins.filter (h: verdicts.${h}.flag == "U") (builtins.attrNames verdicts);

      # The model is checked where it is READ, not before: with nothing labelled `reached` never reads
      # it, and a degenerate subject that carries no model of its own (gen-inspect's, gen-demo's C25)
      # is a legitimate caller of that read-free path.
      reached =
        if labelled == [ ] then
          [ ]
        else
          builtins.seq (checkModelRecord "gen-program.ruleEdges" model) (
            if unsolved != [ ] then
              throw "gen-program.ruleEdges: ${
                quoteAll (prelude.unique (map (d: d.head) unsolved))
              } is labelled by a declaration that is not a rule of this model; the model was solved from other declarations, so it cannot answer for these"
            else if !model.complete then
              throw "gen-program.ruleEdges: the relation is still growing (complete = false), so an edge set read from it would assert a negative for every absent candidate that a later pass may still falsify; read `reached` from the pass that closes the relation, or one membership's answer through the model's `resolve`"
            else if undefined != [ ] then
              throw "gen-program.ruleEdges: ${quoteAll undefined} is UNDEFINED (U); an edge has no third value, so the membership can be carried into the graph neither as an edge nor as its absence, and is refused rather than collapsed. Read its answer through the model's `resolve` and handle 'U'"
            else
              builtins.attrValues (prelude.filterAttrs (h: _: verdicts.${h}.included) settledKeyed)
          );
    in
    {
      inherit candidates reached;
    };
in
{
  inherit ruleEdges;
}
