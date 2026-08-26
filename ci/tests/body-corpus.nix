# ORACLES O2 + O3 — the corpus is expressible, and THE WALK READS WHAT THE FIRING PRODUCES.
#
# Per policy, three claims: the transcription is ADMITTED by the construction walk; the derived
# codomain equals the spec's O3 table row; and the derivation — which fires nothing — equals the
# codomain OBSERVED by actually firing the body at a real, non-sentinel context (guards true,
# registry populated). The last is defect C's retirement witness: the five nix-config sites
# declared their codomains BECAUSE firing at a sentinel recovered the empty head, and here the
# walk reads all five right without firing at all.
#
# ★ THE ADJUDICATED DELTA, asserted rather than smoothed over: fleet.nix:52 hand-declares
# `binds = [ "accessGroups" ]` and the walk finds `[ "accessGroups" "host" ]` — the declaration
# was a hand-maintained under-count (the firing at :81-83 confirms `host` is a payload key), and
# the oracle adjudicates AGAINST the walk's answer being trimmed to match the site.
{
  genProgram,
  prelude,
  ...
}:
let
  fixtures = import ./_fixtures/bodies.nix { inherit prelude genProgram; };
  inherit (fixtures) corpus observe;

  # One cell triple per policy, generated so no policy can silently drop out of the suite.
  perPolicy = prelude.mapAttrsToList (name: p: {
    "test-${name}-is-admitted-by-the-walk" = {
      expr = p.body.refused or false;
      expected = false;
    };
    "test-${name}-derives-its-table-row-without-firing" = {
      expr = genProgram.deriveCodomain p.body;
      expected = p.derived;
    };
    "test-${name}-derivation-equals-the-firing-observation-at-a-real-context" = {
      expr = observe p.body p.ctx;
      expected = p.derived;
    };
  }) corpus;

  merged = builtins.foldl' (a: b: a // b) { } perPolicy;
in
{
  flake.tests.bodyCorpus = merged // {
    # The suite quantifies over the whole table — seven policies, three cells each. A policy
    # dropped from the fixture would shrink this count silently otherwise.
    test-the-corpus-carries-all-seven-policies = {
      expr = builtins.length (builtins.attrNames corpus);
      expected = 7;
    };

    # ── O2: THE FIVE HAND-DECLARED nix-config CODOMAINS, REPRODUCED BY READING ──
    # Each was declared on firing-impossibility grounds; the walk reads it at registration.
    test-o2-fleet-nix-52-binds-superset-with-the-adjudicated-host-key = {
      expr = (genProgram.deriveCodomain corpus.env-to-hosts.body).binds;
      expected = [
        "accessGroups"
        "host"
      ];
    };
    test-o2-home-platform-nix-39-emits-delivery = {
      expr = (genProgram.deriveCodomain corpus.homeAarch64-to-hm.body).emits;
      expected = [ "delivery" ];
    };
    test-o2-nix-on-droid-nix-106-suppresses-user-to-host = {
      expr = (genProgram.deriveCodomain corpus.drop-user-to-host-on-droid.body).suppresses;
      expected = [ "user-to-host" ];
    };
    test-o2-defaults-nix-169-and-189-emit-edge-twice = {
      expr = map (n: (genProgram.deriveCodomain corpus.${n}.body).emits) [
        "user-aspect-auto-include"
        "primary-user-for-owner"
      ];
      expected = [
        [ "edge" ]
        [ "edge" ]
      ];
    };

    # ── THE OBSERVER DISCRIMINATES ──
    # The derivation-equals-observation cells above are equalities, and an equality passed by two
    # broken sides is not a measurement: at a SENTINEL context (guards false), the observation is
    # the recovered empty head and the equality FAILS — same instrument, same run.
    test-control-at-a-sentinel-context-the-observation-recovers-the-empty-head = {
      expr =
        observe corpus.drop-user-to-host-on-droid.body { host.class = "nixos"; }
        == corpus.drop-user-to-host-on-droid.derived;
      expected = false;
    };
  };
}
