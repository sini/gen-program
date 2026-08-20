# Purity invariant: gen-program's library source imports NO `nixpkgs` lib. This pins "pure" as a
# checked property rather than an aspiration — a stray nixpkgs input, a module-system token, or a
# `{ lib, … }` signature creeping into the library source fails CI.
#
# ★ THE MODULE-SYSTEM TOKENS ARE THE SHARPER HALF FOR THIS LIBRARY, AND FOR A REASON THAT IS ABOUT
# ITS PLACE RATHER THAN ITS STYLE. This library exists to REACH the sole evaluator's front door,
# which is precisely why it sits adjacent to the framework toolkit rather than inside it. An
# `evalModules` or `mkOption` appearing here would be this library growing an evaluation of its
# own — a second semantics beside the one it was built to call, which is the failure the whole
# placement argument turns on.
#
# Scope: lib/**.nix + the root flake.nix + default.nix (the library and its flake). NOT ci/ — the
# test harness legitimately uses the nixpkgs lib, including to run this scan.
{ genPrelude, lib, ... }:
let
  libDir = ../../lib;

  # Comment-stripped source: drop everything from the first `#` on each line. Safe here because `#`
  # appears only in comments across these files (no `#` in string literals); documentation may
  # freely mention forbidden tokens without tripping the invariant.
  stripComments =
    text:
    lib.concatStringsSep "\n" (
      map (line: lib.head (lib.splitString "#" line)) (lib.splitString "\n" text)
    );

  # Recursive walk, so the scan keeps covering `lib/` as the library grows past its four modules.
  walk =
    dir:
    lib.concatLists (
      lib.mapAttrsToList (
        name: type:
        if type == "directory" then
          walk (dir + "/${name}")
        else if lib.hasSuffix ".nix" name then
          [ (dir + "/${name}") ]
        else
          [ ]
      ) (builtins.readDir dir)
    );

  sources =
    map (p: {
      name = toString p;
      code = stripComments (builtins.readFile p);
    }) (walk libDir)
    ++
      map
        (rel: {
          name = rel;
          code = stripComments (builtins.readFile (../.. + "/${rel}"));
        })
        [
          "flake.nix"
          "default.nix"
        ];

  forbidden = [
    "nixpkgs" # a nixpkgs flake input / reference
    "lib." # any nixpkgs lib call (lib.types, lib.genAttrs, …)
    "{ lib }" # the old `{ lib }` parameter signature
    "{ lib," # `{ lib, … }` parameter signature
    "evalModules" # module-system tier
    "mkOption" # module-system tier
  ];

  violations = lib.concatMap (
    src:
    map (tok: "${src.name}: '${tok}'") (lib.filter (tok: genPrelude.hasInfix tok src.code) forbidden)
  ) sources;

  # Positive control for the scan itself: the same predicate, in the same run, over a string that
  # DOES contain a forbidden token. An empty `violations` above is evidence only if this is
  # non-empty — otherwise a broken `hasInfix` or an empty `sources` would report clean.
  controlViolations = lib.filter (
    tok: genPrelude.hasInfix tok "let x = evalModules { }; in x"
  ) forbidden;
in
{
  flake.tests.purity = {
    test-library-source-is-nixpkgs-lib-free = {
      expr = violations;
      expected = [ ];
    };

    # The scan reaches real files with real content. A vacuous `sources` — an empty lib/, a readDir
    # that found nothing — would report the invariant clean without testing it, so the
    # non-emptiness is asserted rather than assumed.
    test-scan-reads-non-empty-sources = {
      expr = sources != [ ] && lib.all (s: s.code != "") sources;
      expected = true;
    };

    test-control-forbidden-token-scan-is-live = {
      expr = controlViolations;
      expected = [ "evalModules" ];
    };
  };
}
