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

  # ★ THE STRIP'S PREMISE, asserted rather than assumed. `stripComments` cuts each line at a comment
  # marker, and that cut is sound only while the `#` it cuts at stands OUTSIDE a string literal.
  # Where it does not, live code is truncated to the end of that line and every cell below goes
  # blind on what was removed, with no signal at all — a green suite over source nothing scanned.
  #
  # The predicate asks the strip ITSELF where it cut: `stripComments` of a single line is exactly
  # the text before that line's cut. It then asks whether that text closed every double quote it
  # opened, an odd count meaning the cut stands inside a string. Deriving it from `stripComments`
  # rather than restating the cut rule is what keeps premise and strip from drifting apart when one
  # of them is edited, and it is why one block serves both strip families in this ecosystem.
  #
  # It is LINE-LOCAL and so cannot conclude about string content that spans lines — an indented
  # multi-line string block. Those files are declared as a list of their own by
  # `test-strip-premise-multiline-strings` rather than trusted in silence.
  countQuotes = s: (lib.length (lib.splitString "\"" s)) - 1;
  cutIsInString =
    line:
    let
      kept = stripComments line;
    in
    kept != line && lib.mod (countQuotes kept) 2 == 1;

  # premiseBreaches : [ { name; text; } ] -> [ "file:line" ]. A breach is reported at its line as
  # well as its file, because what it says is that one particular line's code was truncated.
  premiseBreaches =
    srcs:
    lib.concatMap (
      src:
      lib.concatLists (
        lib.imap1 (i: line: lib.optional (cutIsInString line) "${src.name}:${toString i}") (
          lib.splitString "\n" src.text
        )
      )
    ) srcs;

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

  # ★ THE READ AND THE STRIP ARE SEPARATE STAGES, one `readFile` per file feeding both. The premise
  # cell has to speak about the RAW text, which is only a value once the strip stops happening inside
  # the read; and `sources` is then a total per-element function of `rawSources` — the name passes
  # through, the code is the strip of the text — so pinning either one pins the other, and the cells
  # over each COMPOSE instead of hoping two independent reads of the same tree agree.
  rawSources =
    map (p: {
      name = toString p;
      text = builtins.readFile p;
    }) (walk libDir)
    ++
      map
        (rel: {
          name = rel;
          text = builtins.readFile (../.. + "/${rel}");
        })
        [
          "flake.nix"
          "default.nix"
        ];

  sources = map (s: {
    inherit (s) name;
    code = stripComments s.text;
  }) rawSources;

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

    # ★ THE PREMISE HOLDS OF THE TEXT THAT WAS ACTUALLY SCANNED. This is an absence claim over text
    # read from disk and it is NOT non-vacuous on its own: its expectation is `[ ]`, which an emptied
    # or constant subject satisfies exactly as a sound corpus does — a scan of nothing breaches no
    # premise. What arms it is the subject-pinning asserted over this same `rawSources` read, together
    # with the live control below for the predicate itself; green here means the premise holds of the
    # text those cells pin, and nothing more.
    test-strip-premise-holds = {
      expr = premiseBreaches rawSources;
      expected = [ ];
    };

    # And the predicate is capable of saying no. Its subject is a literal written inside this cell
    # rather than anything on disk, so it is UNSEVERABLE from the tree and establishes exactly that the
    # test discriminates an in-string `#` from an ordinary trailing comment — it says nothing whatever
    # about what the cell above was pointed at, and it is NOT that cell's arming. Both directions ride
    # in one expectation: line 1 must be caught and line 2 must not, so a predicate stuck at either
    # constant reds here. The literal cuts under BOTH strip families in this ecosystem — its `#` is
    # whitespace-preceded, so a comment-start strip cuts there too and the control cannot go dead by
    # being pasted into a repository whose strip is the other one.
    test-strip-premise-scan-is-live = {
      expr = premiseBreaches [
        {
          name = "<in-string-hash>";
          text = ''
            url = "a b # c";
            x = 1; # an ordinary trailing comment
          '';
        }
      ];
      expected = [ "<in-string-hash>:1" ];
    };

    # The declared surface: the files the line-local predicate cannot conclude about. An indented
    # multi-line string block carries string content across line boundaries, where a per-line quote
    # count cannot follow it, so those files are written down rather than trusted in silence. The first
    # file to grow one arrives as a red that has to be READ, exactly as a new library file arrives as a
    # red on a membership manifest.
    test-strip-premise-multiline-strings = {
      expr = map (s: s.name) (lib.filter (s: genPrelude.hasInfix "''" s.text) rawSources);
      expected = [ ];
    };
  };
}
