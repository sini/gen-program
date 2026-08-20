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
# ── THE RECORDED LADDER, RE-DERIVED UNDER THE INTERPRETATION PARAMETER ──
# `reDerivationOwedOn` named four constructions and THIS WORK CHANGED TWO OF THEM — the stability
# test (now seeded with `Pos(I)`) and gen-scope's least-model door (now takes a starting set) — so
# a re-derivation was owed by the budget's own stated trigger, not as a follow-up.
#
# `unstable`, one adjudication per reading, wall clock, on the environment terms below:
#
#   u=14   16,384 candidates   0.33 – 0.73 s
#   u=15   32,768 candidates   1.34 – 1.45 s
#   u=16   65,536 candidates   1.28 – 1.31 s   (five readings)
#   u=17  131,072 candidates   2.57 – 5.12 s   ← exceeds the criterion on its worst of five
#   u=18  262,144 candidates   6.64 – 9.27 s
#
# ⇒ **THE FIGURE IS RE-DERIVED AND DOES NOT MOVE: 16.** That is a result rather than a
# non-event — the seeded fixpoint adds a CONSTANT to each candidate's cost, not an exponent, so the
# curve shifts without changing where it crosses the criterion. A re-derivation that reproduces its
# predecessor is still a re-derivation; what would have been dishonest is not running it.
#
# ★ THE CRITERION IS READ AGAINST THE WORST READING, NOT THE BEST. u=17's spread straddles the
# line and a figure taken from its luckiest run is one nobody else can reproduce.
#
# ★★ MEASURING REFUTED AN ASSUMPTION THAT LOOKED SAFE, AND THE ARM STAYS WITH ITS REASON
# CORRECTED. `anticorrelated` was written up as the CHEAP corner because a program WITH stable
# models short-circuits. It does — but where the first stable model sits in the enumeration is a
# property of the program, and for that family it sits exactly ONE THIRD of the way through at
# every rung (86/256, 1366/4096, 21846/65536). Having stable models buys a FACTOR OF THREE, never
# an exponent, so a budget derived from it would price the same curve one rung lower and call it
# safety. The worst-case arm is the honest instrument.
#
# ── THE CARRIED RECOVERY, WHICH IS WHERE THE PARAMETER ACTUALLY PAYS ──
# Under the retired boundary each carried atom brought a PARTNER into the Herbrand base, so a pass
# carrying `n` contested atoms forward arrived at the next pass with roughly TWICE the contested
# count — measured `2n+1` — and the budget was effectively HALVED in carried terms: about 7 atoms
# could cross one boundary. The partners are gone.
#
# ★★ AND WHAT REPLACES THE `2n` IS NOT A CONSTANT. The contested count at pass *N+1* is the carried
# set CLOSED UNDER REACHABILITY in this pass's program, over **BOTH SIGNS** — carried undefinedness
# propagates through a POSITIVE body (through the overestimate's seeded fixpoint) exactly as it
# does through negation. Measured on `ci/bench/coherence-cost.nix`'s three-axis `carriedAt n p q`:
#
#   n=4  p=0  q=0   ⇒ contested 4     the partners are gone: n carried costs n
#   n=4  p=4  q=0   ⇒ contested 8     the positive readers close in
#   n=4  p=0  q=4   ⇒ contested 8     and so do the negative ones — a family holding this axis
#                                     fixed could not see half the closure at all
#   n=4  p=2  q=2   ⇒ contested 8     n + p + q
#   n=2  p=1  q=1   ⇒ contested 4
#
# ⇒ **THE BUDGET IS NO LONGER HALVED IN CARRIED TERMS**: about 16 atoms may cross one boundary
# where before about 7 could, less whatever this pass's program reads from them.
# ★★ AND IT IS AN UPPER BOUND, NOT AN IDENTITY. A reader whose body cannot be satisfied does not
# become contested, so the count is bounded by the sign-blind closure and is generally smaller. A
# budget derived as though the bound were exact would price a worst case the workload may never
# reach — safe in direction, and this file calls it a bound.
#
# ── WHAT THE OTHER TWO FAMILIES MEASURED, because they check the design rather than the figure ──
#   mixed    — a contested corner of four beside a settled bulk of 10, 100 and 400 atoms costs
#              0.04 s and tests 6 candidates AT ALL THREE SIZES. That is Corollary 5.7's
#              restriction working: the budget prices the contested corner and not the program.
#   carried  — the three-axis family above.
{
  # The greatest CONTESTED count at which the exhaustive candidate walk is run. Contested, not
  # atoms: Van Gelder, Ross & Schlipf 1991 Corollary 5.7 bounds every stable model to
  # `trueAtoms ∪ S` for `S ⊆ undefinedAtoms`, so the walk is 2^u in the undefined count and flat
  # in everything else. A bound on the Herbrand base would price the wrong axis.
  contested = 16;

  derivation = "the greatest contested count u at which EVERY reading of the worst-case arm of ci/bench/coherence-cost.nix — the exhaustive `unstable` family, in which no candidate is stable and none short-circuits — completed a single adjudication in under 5 seconds of wall clock, over at least three readings per rung, under the environment terms recorded beside it";

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
  # ★ RE-STATED, because two of the four moved under this work and a trigger naming a construction
  # that no longer exists cannot fire. The stability test is now SEEDED with `Pos(I)`, and the
  # least-model door now takes a STARTING SET on both arms; the seeding of the engine's two
  # operators is new and is named, because it is what determines the contested count the budget
  # prices.
  reDerivationOwedOn = [
    "the candidate enumeration in stable-model.nix"
    "the SEEDED stability test in stable-model.nix"
    "gen-scope's reduct"
    "gen-scope's least-model door, and the starting set it takes"
    "gen-scope's two seeded operators, which fix the contested count"
  ];
}
