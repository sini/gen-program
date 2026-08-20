# THE MEASURED WORKLOAD, AS DECLARATIONS — the shape den v1 ships, not one invented for a suite.
#
# `reports/den-v1-include-semantics-v0.md` measures den v1 at `ecaefcb`: `mkGuardCtx` builds
# `hasAspect` from the IN-FLIGHT `pathSetByScope` and composes a NEGATION over the mid-walk exclude
# registry — `pathSet ? k && !excludeCheck k` — and two named fixpoint loops iterate to stability
# under `maxPolicyIterations = 10` with a throw on cycle. v1's own test comment states the chain:
# "Guard A depends on aspect X which only enters the pathSet because Guard B passed and emitted it."
#
# ★ THE ATOM NAMES BELOW ARE THE FIXTURE'S, NOT THE LIBRARY'S. The library mints no atom name from
# a scheme of its own (`den-hoag-h2yp` law 2, spec R§1.7); these strings are what a caller writes,
# and the shape they spell — a colon-joined pair — is this fixture's convention and travels no
# further than this file.
{ }:
rec {
  # ── THE CHAIN v1's OWN TEST COMMENT DESCRIBES ──
  # `guardB` holds outright; it emits membership X; guard A reads X while NEGATING X's exclusion;
  # guard A then emits membership Y. The negation is over a member of the same growing set, which
  # is the whole reason this shape needs a semantics rather than an iteration cap.
  growingInclude = [
    {
      head = "guard:B";
      relata = [ ];
    }
    {
      head = "member:X";
      pos = [ "guard:B" ];
      relata = [ ];
    }
    {
      head = "guard:A";
      pos = [ "member:X" ];
      neg = [ "excluded:X" ];
      relata = [ ];
    }
    {
      head = "member:Y";
      pos = [ "guard:A" ];
      relata = [ ];
    }
  ];

  # THE MUTANT: the identical declarations with the NEGATION REMOVED. Every other term is
  # untouched, so an assertion that does not discriminate on `neg` accepts both.
  growingIncludeWithoutNegation = [
    {
      head = "guard:B";
      relata = [ ];
    }
    {
      head = "member:X";
      pos = [ "guard:B" ];
      relata = [ ];
    }
    {
      head = "guard:A";
      pos = [ "member:X" ];
      relata = [ ];
    }
    {
      head = "member:Y";
      pos = [ "guard:A" ];
      relata = [ ];
    }
  ];

  # A PRESENTATION PERMUTATION of `growingInclude` — the same four declarations, written in a
  # different order. Nothing about the logical content changes; only the order they arrive in.
  growingIncludePermuted = [
    (builtins.elemAt growingInclude 3)
    (builtins.elemAt growingInclude 1)
    (builtins.elemAt growingInclude 0)
    (builtins.elemAt growingInclude 2)
  ];

  # ── PAST v1's CAP ──
  # A chain of guard→member→guard links longer than v1's `maxPolicyIterations = 10`, where each
  # guard depends on the member the previous guard emitted. v1 caps at ten and throws on the
  # eleventh; here it is a program with a model.
  capLength = 15;

  longChain = [
    {
      head = "link:0";
      relata = [ ];
    }
  ]
  ++ builtins.concatLists (
    builtins.genList (i: [
      {
        head = "emitted:${toString i}";
        pos = [ "link:${toString i}" ];
        relata = [ ];
      }
      {
        head = "link:${toString (i + 1)}";
        pos = [ "emitted:${toString i}" ];
        relata = [ ];
      }
    ]) capLength
  );
}
