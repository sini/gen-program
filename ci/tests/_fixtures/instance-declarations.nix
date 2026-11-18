# THE BRIDGE'S FIXTURES — invented policies over one vocabulary (a sewing room: `pleat`, `hem`,
# `baste`), read by the value plane (`ci/tests/instance-declarations.nix`) and the error plane
# (`ci/tests-error.nix`), so the two planes assert over one set of bodies and namers.
#
# The caller names every atom here, as a framework would: `factByContent` names a fact by its
# constructor, kind and payload, so two policies firing the same content name ONE fact (two
# supports); `abLocal` keys an abnormality by policy and context identifier, `abGlobal` by policy
# alone.
{
  prelude,
  genProgram,
  T,
}:
let
  inherit (T.term)
    has
    lit
    readCtx
    ;
  gp = genProgram;
  B = gp.instanceDeclarations;

  content = v: if v ? payload then builtins.toJSON v.payload else builtins.toJSON v.target;
  factByContent = v: {
    head = "${v.ctor}:${v.kind or ""}:${content v}@${v.at}";
    relata = [ ];
  };
  factByPolicy = v: {
    head = "${v.ctor}:${v.policy}@${v.at}";
    relata = [ ];
  };
  abLocal =
    { policy, at }:
    {
      head = "ab:${policy}@${at}";
      relata = [ ];
    };
  abGlobal =
    { policy, ... }:
    {
      head = "ab:${policy}";
      relata = [ ];
    };
  local = {
    fact = factByContent;
    abnormal = abLocal;
  };

  declared = [
    "spool"
    "lint"
  ];
  member = thread: {
    ctor = "member";
    kind = "trim";
    when = has "spool";
    payload.thread = lit thread;
  };
  sup = t: {
    ctor = "suppress";
    target = t;
  };
  mkB =
    name: clauses:
    gp.body {
      inherit name declared clauses;
    };

  ctx = {
    spool.fibre = "silk";
  };
  at = a: body: {
    inherit body;
    context = ctx;
    sources.spool = "spool:${a}";
    at = a;
    when = has a;
  };
  facts =
    map
      (a: {
        head = a;
        relata = [ ];
      })
      [
        "bolt:a"
        "bolt:b"
      ];

  solveWith =
    complete: frozen: decls:
    gp.model {
      program = gp.program frozen (facts ++ decls);
      interpretation = [ ];
      inherit complete;
      prior = null;
    };
  solve = solveWith true [ ];
  read =
    m: a:
    let
      r = m.resolve a;
    in
    if r.flag == "U" then
      "U"
    else if r.included then
      "T"
    else
      "F";
  verdicts =
    names: apps: atoms:
    let
      m = solve (B names apps).declarations;
    in
    builtins.listToAttrs (
      map (a: {
        name = a;
        value = read m a;
      }) atoms
    )
    // {
      adjudication = m.adjudication.outcome;
    };

  # The fact of pleat's (and baste's) silk member at bolt:a / bolt:b, and of hem's wool member.
  pf = ''member:trim:{"thread":"silk"}@bolt:a'';
  pfb = ''member:trim:{"thread":"silk"}@bolt:b'';
  hf = ''member:trim:{"thread":"wool"}@bolt:a'';
in
rec {
  inherit
    B
    gp
    local
    abLocal
    abGlobal
    factByContent
    factByPolicy
    content
    member
    sup
    mkB
    ctx
    at
    facts
    solve
    solveWith
    read
    verdicts
    pf
    pfb
    hf
    ;

  pleat = mkB "pleat" [ (member "silk") ];
  baste = mkB "baste" [ (member "silk") ];
  hem = mkB "hem" [ (sup "pleat") ];
  snip = mkB "snip" [ (sup "baste") ];
  hemCutter = mkB "baste-cutter" [ (sup "hem") ];
  pleatC = mkB "pleat" [
    (member "silk")
    (sup "hem")
  ];
  hemC = mkB "hem" [
    (member "wool")
    (sup "pleat")
  ];
  selfish = mkB "pleat" [
    (member "silk")
    (sup "pleat")
  ];
  hemGuarded = mkB "hem" [ ((sup "pleat") // { when = has "lint"; }) ];

  # A read-free body: its firing mint is equal at two contexts.
  tack = mkB "tack" [
    {
      ctor = "member";
      kind = "trim";
      payload.x = lit 1;
    }
  ];
  # A member and a deliver with an equal condition and payload: the producer mints them apart.
  seam = mkB "seam" [
    {
      ctor = "member";
      kind = "trim";
      payload.x = lit 1;
    }
    {
      ctor = "deliver";
      payload.x = lit 1;
    }
  ];
  # The same pair, but two kinds of member.
  twoKinds = mkB "tuck" [
    {
      ctor = "member";
      kind = "trim";
      payload.x = lit 1;
    }
    {
      ctor = "member";
      kind = "facing";
      payload.x = lit 1;
    }
  ];
  rawMints =
    b: a: map (d: d.__mint.minted) (gp.groundInstances { sources.spool = "spool:${a}"; } ctx b);

  twoClause =
    order:
    mkB "pleat" (
      if order then
        [
          (member "silk")
          (member "wool")
        ]
      else
        [
          (member "wool")
          (member "silk")
        ]
    );

  # A deliver whose payload throws one level down if read.
  bundle = mkB "bundle" [
    {
      ctor = "deliver";
      when = has "spool";
      payload.cargo = readCtx "spool" [ "cargo" ];
    }
  ];
  sentinelApp = {
    body = bundle;
    context.spool = {
      cargo.inner = throw "instance-declarations fixture: the delivered content was forced";
    };
    sources.spool = "spool:a";
    at = "bolt:a";
    when = has "bolt:a";
  };

  # A door clause whose output carries no `__mint`, and one carrying a sixth constructor.
  doorBody = gp.body {
    name = "weld";
    declared = null;
    clauses = [
      {
        body = T.term.ref ''{"declared":"w"}'';
        emits = [ "trim" ];
        binds = [ ];
        suppresses = [ ];
      }
    ];
  };
  doorApp = out: {
    body = doorBody;
    context = { };
    at = "bolt:a";
    when = has "bolt:a";
    door = _: {
      right = {
        output = out;
        scope = { };
      };
    };
  };
  twoOut = [
    {
      ctor = "member";
      kind = "trim";
      payload.x = 1;
    }
    {
      ctor = "member";
      kind = "trim";
      payload.x = 2;
    }
  ];

  # Collisions.
  otherPleat = mkB "pleat" [ (member "linen") ];
  memberAndDeliver = mkB "seam" [
    (member "silk")
    {
      ctor = "deliver";
      when = has "spool";
      payload.thread = lit "silk";
    }
  ];
  ctorBlind = {
    fact = v: {
      head = "f:${content v}@${v.at}";
      relata = [ ];
    };
    abnormal = abLocal;
  };
  factAsAb = {
    fact = v: {
      head = "ab:hem@${v.at}";
      relata = [ ];
    };
    abnormal = abLocal;
  };
  setHead = {
    fact = _: {
      head = { };
      relata = [ ];
    };
    abnormal = abLocal;
  };
  # Namers returning a field outside their closed result: a `when` the bridge would overwrite, and
  # a `label` the abnormality would drop.
  factWithWhen = {
    fact = v: factByContent v // { when = T.term.not (has "bolt:a"); };
    abnormal = abLocal;
  };
  abWithLabel = {
    fact = factByContent;
    abnormal = a: abLocal a // { label = "seam"; };
  };
  unsourced = {
    body = mkB "pleat" [ (member "silk") ];
    context = ctx;
    at = "bolt:a";
    when = has "bolt:a";
  };

  # All five constructors in one body; the edge named with relata and a label.
  weave = gp.body {
    name = "weave";
    declared = [ "spool" ];
    clauses = [
      (member "silk")
      {
        ctor = "edge";
        when = has "spool";
        target = lit "overlock";
      }
      (sup "hem")
      {
        ctor = "deliver";
        payload.x = lit 1;
      }
      {
        ctor = "realize";
        target = lit "loom";
      }
    ];
  };
  fiveNames = {
    abnormal = abLocal;
    fact =
      v:
      if v.ctor == "edge" then
        {
          head = "edge:${v.at}>${v.target}";
          relata = [
            v.at
            v.target
          ];
          label = "stitch";
        }
      else
        factByPolicy v;
  };

  # G14 · an iteration over `bolts`: `reelOf ctor` emits one `ctor` per item, its payload the item.
  # A keyed `bolts` identifies each item by its name; a list `bolts` by its position.
  reelOf =
    ctor:
    gp.body {
      name = "reel-${ctor}";
      declared = [ "bolts" ];
      clauses = [
        (gp.forEach {
          over = readCtx "bolts" [ ];
          emit = [
            (
              {
                inherit ctor;
                when = has "bolts";
                payload.thread = readCtx "item" [ ];
              }
              // (if ctor == "member" then { kind = "reel"; } else { })
            )
          ];
        })
      ];
    };
  reelAt = ctor: bolts: {
    body = reelOf ctor;
    context = { inherit bolts; };
    sources.bolts = "bolts:a";
    at = "bolt:a";
    when = has "bolt:a";
  };
  # The firing identity of the item whose thread is `thread`.
  idOfThread =
    r: thread:
    builtins.filter (id: r.firings.${id}.payload.thread == thread) (builtins.attrNames r.firings);

  perms =
    xs:
    if xs == [ ] then
      [ [ ] ]
    else
      builtins.concatMap (
        i:
        let
          x = builtins.elemAt xs i;
          rest = builtins.genList (j: builtins.elemAt xs (if j < i then j else j + 1)) (
            builtins.length xs - 1
          );
        in
        map (p: [ x ] ++ p) (perms rest)
      ) (builtins.genList (i: i) (builtins.length xs));
  permApps = [
    (at "bolt:a" pleat)
    (at "bolt:b" pleat)
    (at "bolt:a" hem)
    (at "bolt:a" hemCutter)
  ];
  distinct = xs: builtins.length (prelude.unique xs);
}
