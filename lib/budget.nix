# THE RECORDED FIGURE, AND ITS DERIVATION, AS DATA.
#
# It lives in its own file for one reason: the construction it bounds is the thing the cost curve
# has to be measured ON, so a derivation run must be able to reach that construction PAST the
# figure. `ci/bench/coherence-cost.nix` imports `stable-model.nix` directly with a raised
# `contested` to plot the ladder this figure is then read off.
#
# ★ THAT DOES NOT MAKE THE BUDGET A MODE A CALLER SELECTS, AND THE DIFFERENCE IS STRUCTURAL. The
# published surface (`lib/default.nix`) wires exactly this record and exposes it as
# `stableModelBudget` — a value to READ. There is no argument anywhere on `.lib` through which a
# consumer can supply a different one, so a caller cannot select the budget under which their own
# program is adjudicated. Only a derivation run, importing the module directly, can — which is
# what makes the recorded figure re-derivable instead of a number nobody can check.
#
# ── THE FIGURE IS NEVER A BARE NUMBER ──
# It is derived at implementation from this library's own measured cost curve and recorded WITH
# its derivation, so a later reader can say what it means and re-derive it, and it is re-derived
# whenever the constructions below change (ADR-0032 ruling 5). "Changes" is made checkable rather
# than left to judgement: `reDerivationOwedOn` names the constructions whose editing owes one.
#
# ── THE DERIVATION READS THE WORST-CASE ARM, AND THE MEASUREMENT SAYS WHY ──
# The `unstable` family has NO stable model anywhere, so its walk is EXHAUSTIVE: all 2^u
# candidates are built and tested and none short-circuits.
#
# ★★ AND THE SHORT-CIRCUIT TURNS OUT TO BE A CONSTANT FACTOR RATHER THAN AN ORDER REDUCTION, WHICH
# IS THE MEASUREMENT'S OWN CORRECTION TO AN ASSUMPTION THAT LOOKED SAFE. A program that HAS stable
# models stops at the first one it reaches — but where that one sits in the enumeration is a
# property of the program, not a small number. Measured on `anticorrelated`, whose k independent
# two-cycles have 2^k stable models: the walk tests **exactly one third** of the space at every
# rung (86/256, 1366/4096, 21846/65536 — 33.6%, 33.3%, 33.3%). ⇒ Having stable models buys a
# factor of three, not an exponent, so a budget derived from that family would price the same
# curve one rung lower and call it safety. The worst-case arm is the honest instrument.
#
# ── THE RECORDED LADDER, from which the figure below is read ──
# `unstable`, one adjudication per reading, three readings per rung, wall clock:
#
#   u=15   32,768 candidates   0.81 – 1.43 s
#   u=16   65,536 candidates   1.29 – 1.59 s
#   u=17  131,072 candidates   2.61 – 5.65 s   ← exceeds the criterion on its worst reading
#   u=18  262,144 candidates   7.78 s
#
# ★ THE CRITERION IS READ AGAINST THE WORST READING, NOT THE BEST. u=17's spread straddles the
# line, and a figure taken from its luckiest run would be a figure nobody else can reproduce.
#
# ── WHAT THE OTHER TWO FAMILIES MEASURED, because they check the design rather than the figure ──
#   mixed    — a contested corner of four beside a settled bulk of 10, 100 and 400 atoms costs
#              0.04 s and tests 6 candidates AT ALL THREE SIZES. That is Corollary 5.7's
#              restriction working: the settled bulk does not enter the search, so the budget
#              genuinely prices the contested corner and not the program.
#   carried  — the pass-boundary construction introduces one partner per carried atom, so a pass
#              carrying n contested atoms forward arrives at the next pass with ROUGHLY TWICE the
#              contested count (measured 2n+1 in that fixture, the extra one being the reader that
#              depends on them). ⇒ THE BUDGET IS EFFECTIVELY HALVED IN CARRIED TERMS: about 7
#              atoms may be carried across one boundary before the next pass's adjudication goes
#              NOT-EVALUATED. That is a real price of the construction and it is recorded rather
#              than discovered.
{
  # The greatest CONTESTED count at which the exhaustive candidate walk is run. Contested, not
  # atoms: Van Gelder, Ross & Schlipf 1991 Corollary 5.7 bounds every stable model to
  # `trueAtoms ∪ S` for `S ⊆ undefinedAtoms`, so the walk is 2^u in the undefined count and flat
  # in everything else. A bound on the Herbrand base would price the wrong axis.
  contested = 16;

  derivation = "the greatest contested count u at which EVERY reading of the worst-case arm of ci/bench/coherence-cost.nix — the exhaustive `unstable` family, in which no candidate is stable and none short-circuits — completed a single adjudication in under 5 seconds of wall clock, over three readings per rung, under the environment terms recorded beside it";

  fixtures = [
    "anticorrelated"
    "carried"
    "mixed"
    "unstable"
  ];

  # Part of the comparison rather than a note beside it: a figure read under a different evaluator
  # or a different call-depth guard is a figure about a different machine.
  environment = {
    nix = "2.34.8";
    maxCallDepth = 10000;
    stackLimitKb = 8192;
  };

  # The constructions whose editing owes a re-derivation, as data rather than as prose, so the
  # trigger's content is one thing and not two that drift.
  reDerivationOwedOn = [
    "the candidate enumeration in stable-model.nix"
    "the stability test in stable-model.nix"
    "gen-scope's reduct"
    "gen-scope's least-model door"
  ];
}
