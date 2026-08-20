# THE COHERENCE GATE'S COST CLASSES — one measurement per (fixture family, contested count),
# reporting the curve the stable-model budget is derived from.
#
# ★ THIS PATH IS A FIXED CITATION TARGET. `lib/stable-model.nix` names it as the suite its
# derivation function reads, and `README.md` cites it as the re-run command behind the recorded
# figure. Add arms and shapes; do not rename.
#
# WHAT IT REPORTS AND WHAT IT DOES NOT. It reports the CURVE. It states no budget and offers no
# figure as one: the figure is a person's reading of this curve against the fleet the library is
# for, and a threshold written here would be a cost bound wearing a correctness face.
#
# ── WHY THE AXIS IS THE CONTESTED COUNT AND NOT THE PROGRAM SIZE ──
# The value path is the well-founded model and it is polynomial; nothing on it is measured here.
# The gate walks candidate interpretations, and Van Gelder, Ross & Schlipf 1991 Corollary 5.7
# bounds every stable model to `trueAtoms ∪ S` for `S ⊆ undefinedAtoms` — so the walk is 2^u in
# the CONTESTED count u and flat in everything else. A curve plotted against the Herbrand base
# would price the wrong axis and would produce a budget that is generous exactly where the cost is.
#
# ── THE FOUR FAMILIES, AND WHY THE LAST ONE IS THE CEILING ──
#
#   anticorrelated — u/2 independent negative two-cycles, so 2^(u/2) stable models. The walk stops
#                    at the first one it reaches.
#                    ★★ AND MEASURING IT REFUTED THE REASON IT WAS WRITTEN. It was put here as the
#                    CHEAP corner; it is not one. Where the first stable model sits in the
#                    enumeration is a property of the program, and for this family it sits exactly
#                    one third of the way through, at every rung measured (86/256, 1366/4096,
#                    21846/65536 — 33.6%, 33.3%, 33.3%). ⇒ having stable models buys a FACTOR OF
#                    THREE, never an exponent. The arm stays, with its reason corrected: it is what
#                    shows the short-circuit is a constant and not a saving the budget may lean on.
#   carried        — n atoms carried across a pass boundary. Each carry introduces one partner, so
#                    the contested count is roughly DOUBLE the carried count — measured 2n+1 here,
#                    the extra one being the reader that depends on them. This is the price of the
#                    boundary construction, paid on the axis that matters, and it is measured
#                    rather than reasoned about.
#   mixed          — a contested corner beside a settled bulk. The bulk must NOT move the cost, and
#                    a curve that rises with it would say the restriction to the contested corner
#                    is not doing what Corollary 5.7 licenses. ★ Measured flat: four contested
#                    atoms cost 6 candidates and 0.04 s beside a bulk of 10, of 100 and of 400.
#   unstable       — u independent `p :- not p`, none of which has a stable model. The walk is
#                    EXHAUSTIVE: every one of the 2^u candidates is built and tested and none
#                    short-circuits. ★ THIS IS THE ARM THE BUDGET IS DERIVED FROM, because a
#                    budget derived from a family that short-circuits would price the corner the
#                    gate does not have to survive.
#
# ── HOW TO READ IT ──
#
#   nix eval --impure --json -f ci/bench/coherence-cost.nix report
#
# Each cell forces its whole row, so what a timing harness measures is the adjudication and not a
# thunk. `outcome` is on every cell: a cell whose outcome is not the family's expected one is not
# a point on the curve, it is a broken fixture.
#
# ★★ THE LADDER RUNS PAST THE RECORDED FIGURE, AND IT HAS TO. The budget gates the very
# construction being measured, so a bench held to it could only ever plot the part of the curve
# the figure already admits — and a derivation that cannot see past its own answer is not a
# derivation. `lib/stable-model.nix` therefore takes the budget as a MODULE PARAMETER, and this
# file supplies a raised one. Nothing on the published `.lib` surface can do the same: a consumer
# reads `stableModelBudget` and cannot select one, which is what keeps this an instrument rather
# than a mode.
let
  ci = builtins.getFlake (toString ../.);
  scope = ci.inputs.gen-scope.lib;
  prelude = ci.inputs.gen-scope.inputs.gen-prelude.lib;
  genProgram = import ../../lib { inherit prelude scope; };

  # The same constructions, with the gate opened far enough to plot the knee. `headroom` is not a
  # candidate figure and is never read as one — it is the edge of the instrument.
  headroom = 26;
  measuringStableModel = import ../../lib/stable-model.nix {
    inherit prelude scope;
    budget = (import ../../lib/budget.nix) // {
      contested = headroom;
    };
  };
  measuring = import ../../lib/model.nix {
    inherit prelude scope;
    stableModel = measuringStableModel;
  };

  declare =
    d:
    d
    // {
      relata = [ ];
    };

  # ── THE FAMILIES ──

  # u/2 negative two-cycles ⇒ u contested atoms, each pair with two stable models.
  anticorrelated =
    u:
    prelude.concatMap (i: [
      (declare {
        head = "a${toString i}";
        neg = [ "b${toString i}" ];
      })
      (declare {
        head = "b${toString i}";
        neg = [ "a${toString i}" ];
      })
    ]) (prelude.genList (i: i) (u / 2));

  # u independent `p :- not p` ⇒ u contested atoms and NO stable model anywhere.
  unstable =
    u:
    prelude.genList (
      i:
      declare {
        head = "p${toString i}";
        neg = [ "p${toString i}" ];
      }
    ) u;

  # A contested corner of four, beside a settled chain of `bulk` atoms.
  mixed =
    bulk:
    anticorrelated 4
    ++ [ (declare { head = "s0"; }) ]
    ++ prelude.genList (
      i:
      declare {
        head = "s${toString (i + 1)}";
        pos = [ "s${toString i}" ];
      }
    ) bulk;

  # ── THE ARMS ──
  # `carried` is the same shape reached through the pass-boundary construction rather than
  # written as declarations, so what it prices is the construction's own contribution.
  row =
    { declarations, carried }:
    let
      built = genProgram.program {
        inherit declarations carried;
        frozen = [ ];
      };
      m = measuring.model {
        inherit built;
        complete = true;
      };
      cell = {
        inherit (m.adjudication)
          outcome
          contested
          searched
          candidatesTested
          ;
        atoms = prelude.length built.program.atoms;
        converged = m.converged;
      };
    in
    builtins.deepSeq cell cell;

  ladder =
    f:
    prelude.listToAttrs (
      map
        (u: {
          name = "u${toString u}";
          value = f u;
        })
        [
          2
          4
          6
          8
          10
          12
          14
          16
        ]
    );
in
{
  # Named arms, so a timing harness can run ONE point rather than the whole grid: the wall clock
  # of a whole ladder is the sum of its rows and says nothing about where the knee is.
  inherit
    anticorrelated
    unstable
    mixed
    ;

  at =
    family: u:
    row {
      declarations =
        if family == "anticorrelated" then
          anticorrelated u
        else if family == "unstable" then
          unstable u
        else
          mixed u;
      carried = [ ];
    };

  # The boundary construction's arm: `n` carried atoms produce `2n` contested ones.
  carriedAt =
    n:
    row {
      declarations = [
        (declare {
          head = "reader";
          pos = [ "x0" ];
        })
      ];
      carried = prelude.genList (i: "x${toString i}") n;
    };

  report = {
    anticorrelated = ladder (
      u:
      (row {
        declarations = anticorrelated u;
        carried = [ ];
      })
    );
    unstable = ladder (
      u:
      (row {
        declarations = unstable u;
        carried = [ ];
      })
    );
  };
}
