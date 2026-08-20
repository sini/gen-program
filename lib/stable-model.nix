# THE COHERENCE CRITERION — stable-model existence, BUILT, and run under a derived budget.
#
# ADR-0020 makes stable-model existence the refusal oracle. gen-scope states in its own README
# that the oracle "is NOT built here", and that containment — well-founded ⊆ every stable model —
# "is what keeps the pair coherent; it is not a decision procedure." So the gate was ruled and
# nothing evaluated it, and every solved program was un-adjudicated by the criterion that governs
# it. Silence then reads as admission, which is this project's one defect. This file is the
# construction that ends that, under the BOUNDED arm the owner ruled.
#
# ── THE SHAPE OF THE RULING, AND IT IS NOT "RUN AN NP SEARCH ON EVERY PROGRAM" ──
# The normal path is POLYNOMIAL and the bounded search is the coherence gate ONLY. The
# well-founded computation is the sole VALUE path: it runs on every program, it is what every
# verdict comes from, and nothing below is on it. The search below decides ADMISSIBILITY, is
# reached only where the model is PARTIAL, and prices only the contested corner.
#
# ★★ THE SHORT-CIRCUIT IS A PUBLISHED RESULT, VERIFIED AT THE ARCHIVED PRIMARY, AND THE
# COORDINATE IS CITED HERE BECAUSE IT IS LOAD-BEARING. Van Gelder, Ross & Schlipf 1991,
# **Corollary 5.6**, verbatim: "If P has a well-founded total model, then that model is the unique
# stable model." (archived transcription, file line 1372). A TOTAL well-founded model — one with
# no undefined atom — therefore CERTIFIES existence by itself, and the search is not merely
# skipped but unnecessary: coherence comes free with the value path.
#
# ★ AND THE CONVERSE IS NOT AVAILABLE, WHICH IS WHY THE PARTIAL CASE GENUINELY HAS TO SEARCH. The
# same paper, immediately below: "In Examples 5.4 and 5.5 below we show that the converse of
# Corollary 5.6 is not necessarily true" (line 1376) — "there also are programs with a unique
# stable model and only a partial well-founded model" (line 1385). A partial model is NOT evidence
# of incoherence, so a construction that refused on partiality would refuse programs the criterion
# admits.
#
# ── WHY THE SEARCH IS BOUNDED AT ALL, STATED AS A COMPLEXITY FACT AND NOT AS A FEELING ──
# The same primary, reporting Marek & Truszczyński: "even for propositional general logic programs
# P, determining whether P has a stable model at all is NP-complete" (line 1849) — against the
# well-founded model's polynomial data complexity, which that paper's Theorem 8.1 establishes.
# That asymmetry is the whole reason this is a bounded gate rather than an unconditional one.
#
# ── THE SEARCH SPACE IS RESTRICTED BY A PUBLISHED RESULT, NOT BY A HEURISTIC ──
# Enumerating every total interpretation would be 2^|Herbrand base|. **Corollary 5.7**: "The
# well-founded partial model of P is a subset of every stable model of P" (line 1373), where a
# partial interpretation is "a consistent SET OF LITERALS whose atoms are in the Herbrand base"
# (Definition 2.4, line 667) — so the subset relation constrains BOTH signs: every stable model
# contains every well-founded TRUE atom and excludes every well-founded FALSE one. The candidates
# are therefore exactly `trueAtoms ∪ S` for `S ⊆ undefinedAtoms`, which is 2^u for u the CONTESTED
# count, and the enumeration is EXHAUSTIVE over stable models rather than a sample of them.
# ⇒ That exhaustiveness is what licenses the `refused` outcome: no candidate stable means no
# stable model, and not merely none found.
#
# ★★ A SECOND WITNESS BESIDE THE PUBLISHED ONE: a differential against an enumerator applying NO
# restriction at all — the full powerset of the Herbrand base, every total interpretation tested
# for stability.
#   · The gate's run (`den-hoag-mpb7`, gate contact), which is the stronger instrument and the one
#     to cite: a negation-biased generator FILTERED to partial well-founded models, giving **188
#     live programs, all of them having stable models** under full-powerset enumeration. Clean
#     **0/188** disagreements against a seeded restriction caught **126/188**.
#   · This library's own, kept beside it because it is the one run here: 17 programs from
#     anticorrelated pairs, settled chains and unstable atoms; the search ran on 16 and 10 of
#     those genuinely have stable models; agreement on every one, with the seeded `S = ∅` defect
#     caught on exactly those 10.
# ★★★ THE POPULATION IS WHAT MAKES EITHER OF THOSE EVIDENCE, AND IT WAS EARNED THE HARD WAY. A
# first attempt here ran 120 RANDOMLY GENERATED programs and also found zero disagreements — and
# its control was DEAD: **in that reproduction** every admitted program had a TOTAL well-founded
# model, so the search path never once ran on a program that HAS a stable model, and narrowing a
# space containing nothing still contains nothing. The tell is an identity worth checking on any
# such run: `admitted` == the count of programs with ZERO contested atoms. ⇒ A zero-disagreement
# differential over this restriction means NOTHING until its population is shown to contain
# partial-model programs that have stable models.
#
# ── STABILITY IS TESTED WITH gen-scope's OWN CONSTRUCTIONS, NEVER A SECOND COPY ──
# Gelfond & Lifschitz: `M` is stable iff `M = lfp T_{P/M}`. The reduct is `scope.reduct` and the
# least fixpoint is `scope.leastModel`, both consumed through that library's published surface.
# Nothing here re-implements a reduct, a fixpoint or a partitioner.
#
# ── ADR-0022's ENGINE CONSTRAINTS BIND THIS LOOP ──
# The candidate walk is a FLAT FOLD over an index list, never a self-applying lambda: Nix does not
# reuse the frame of a call in tail position, so a recursive walk's descent depth is its iteration
# count and past the call-depth guard it aborts — an abort `tryEval` does not contain. Every field
# of the accumulator is forced once per round, and the forcing is `scope.forceFields`, TAKEN from
# the library that defines it rather than written again here: two copies of a discipline agree only
# for as long as someone keeps them in step, and a partial forcing is indistinguishable from none.
#
# ── THE BUDGET IS A DERIVED FIGURE AND NEVER A BARE NUMBER ──
# It is derived at implementation from this library's OWN measured cost curve and recorded WITH
# its derivation, so a later reader can say what it means and re-derive it (ADR-0032 ruling 5, and
# the shape gen-scope's `acceptance.nix` already uses for its verified depth). Past it the field
# below carries NOT-EVALUATED — a named outcome, never a silence and never an admission.
#
# ★ `budget` ARRIVES AS A MODULE PARAMETER AND IS NOT A MODE A CALLER SELECTS. `lib/default.nix`
# wires the one recorded record from `lib/budget.nix`, and the published surface exposes it as a
# value to READ — there is no argument on `.lib` through which a consumer can supply another. The
# parameter exists so a DERIVATION RUN can reach this construction past the recorded figure, which
# is what makes that figure re-derivable rather than a number nobody can check. Its full statement
# and its derivation live in `lib/budget.nix`.
{
  prelude,
  scope,
  budget,
}:
let
  # The closed vocabulary, as data, so a widening fails a cell rather than passing silently — and
  # so a consumer binds a name rather than knowing a string. `not-evaluated` is a MEMBER: past the
  # budget is a real state of this instrument, not an absence of one.
  outcomeNames = [
    "admitted"
    "refused"
    "not-evaluated"
  ];

  criterion = "stable-model existence — ADR-0020's refusal oracle, as Gelfond & Lifschitz define stability and Van Gelder, Ross & Schlipf 1991 relate it to the well-founded model";

  # `2^n`, as a fold rather than a recursion, for the same reason every other loop here is a fold.
  pow2 = n: prelude.foldl' (a: _: a * 2) 1 (prelude.genList (i: i) n);

  # ── THE ADJUDICATION ──
  # Total: every branch returns a NAMED outcome with its ground. There is no path that returns
  # nothing, and none that returns an outcome without saying what decided it.
  adjudicate =
    { program, model }:
    let
      undefined = model.undefinedAtoms;
      contested = prelude.length undefined;
      trueSet = prelude.genAttrs model.trueAtoms (_: true);

      # Bit j of the candidate index selects undefined atom j. `bitAnd` against a precomputed
      # power table keeps the selection flat — Nix publishes no shift builtin, and a per-candidate
      # exponentiation would put a fold inside a fold for a value that does not change.
      powers = prelude.genList pow2 contested;
      positions = prelude.genList (j: j) contested;
      selectedAt =
        i:
        prelude.concatMap (
          j: prelude.optional (builtins.bitAnd i (prelude.elemAt powers j) != 0) (prelude.elemAt undefined j)
        ) positions;
      candidateAt = i: trueSet // prelude.genAttrs (selectedAt i) (_: true);

      # Gelfond–Lifschitz stability, through gen-scope's own reduct and least-model door.
      isStable = guess: (scope.leastModel (scope.reduct program guess)).derived == guess;

      step =
        acc:
        if acc.found then
          acc
        else
          let
            guess = candidateAt acc.index;
            stable = isStable guess;
          in
          {
            found = stable;
            index = acc.index + 1;
            tested = acc.tested + 1;
            # Forced to weak head normal form each round like every other field, which performs
            # the update rather than accumulating one thunk per candidate.
            witness = if stable then guess else acc.witness;
          };

      final = prelude.iterateBounded scope.forceFields step {
        found = false;
        index = 0;
        tested = 0;
        witness = { };
      } (prelude.genList (i: i) (pow2 contested));
    in
    if contested == 0 then
      {
        inherit criterion contested;
        outcome = "admitted";
        reason = "the well-founded model is TOTAL, so it is itself the unique stable model and existence is certified by the value path — no search was needed";
        ground = "Van Gelder, Ross & Schlipf 1991, Corollary 5.6";
        searched = false;
        candidatesTested = 0;
      }
    else if contested > budget.contested then
      {
        inherit criterion contested;
        outcome = "not-evaluated";
        reason = "the well-founded model is PARTIAL and the contested count exceeds the derived budget, so the criterion was not evaluated on this program — this states an ABSENCE of adjudication and is never an admission";
        ground = "the budget recorded beside this construction, with its derivation";
        searched = false;
        candidatesTested = 0;
      }
    else if final.found then
      {
        inherit criterion contested;
        outcome = "admitted";
        reason = "the well-founded model is PARTIAL and a stable model was exhibited within the budget";
        ground = "Gelfond & Lifschitz stability, tested over the candidate space Van Gelder, Ross & Schlipf 1991 Corollary 5.7 bounds";
        searched = true;
        candidatesTested = final.tested;
      }
    else
      {
        inherit criterion contested;
        outcome = "refused";
        reason = "the well-founded model is PARTIAL and the candidate space was walked EXHAUSTIVELY within the budget with no stable model found, so the program has none — ADR-0020's criterion refuses it";
        ground = "Van Gelder, Ross & Schlipf 1991 Corollary 5.7 bounds every stable model to this candidate space, so an exhausted walk is a decision and not a sample";
        searched = true;
        candidatesTested = final.tested;
      };
in
{
  inherit adjudicate;
  # Published under names that say WHICH budget and WHICH criterion. A bare `budget` on a library
  # surface is a number whose axis a reader has to go and find, and this one prices the contested
  # count and nothing else.
  stableModelBudget = budget;
  stableModelCriterion = criterion;
  adjudicationOutcomes = outcomeNames;
}
