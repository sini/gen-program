# THE DECLARATIONS OF FIRED POLICY BODIES: `instanceDeclarations`, the bridge from the policy-body
# algebra (`body`, `groundInstances`) to the rule algebra (`declaration`, `program`).
#
# Spec of record: den-ag-design specs/2026-11-16-gen-program-rules-of-bridge-spec.md (carrier
# den-hoag-rulesof-fold-w9vlp), under its spec gate's conditions.
#
# `instanceDeclarations { fact; abnormal; } applications` fires each application through
# `groundInstances` and returns `{ declarations; firings; }`: the declarations `program` takes, and
# the firings they came from keyed by FIRING identity. Every atom is a string the caller wrote:
# `fact view -> { head; relata; label?; promote?; }` names a member/deliver/edge/realize firing's
# fact, and `abnormal { policy; at; } -> { head; relata; }` names the abnormality a suppress firing
# asserts and every firing of `policy` at `at` is defeated by (McCarthy's pair, as gen-rules'
# catalogue states it). The bridge writes only the BODY: the application's `when`, and `not ab`.
#
# Three identities stay apart: the FACT is the caller's head (two firings naming one head are two
# supports of it), the FIRING is minted here over the interpreter's firing mint plus the policy and
# the context identifier, and the OCCURRENCE (one delivered contribution at one receiver) is not
# constructed here. No list position is an identity: the output is in firing-identity order. A
# `forEach` item is identified by the interpreter: under a keyed `over` by its name, a semantic
# identity; under a list `over` by its index, provenance only, so such a firing's identity moves with
# the order of `over`, and a delivering list iteration is refused by name before it reaches here.
#
# Only fired `suppress` records produce abnormality rules; a declared codomain is never read.
{
  prelude,
  T,
  hashIdentity,
  identityOf,
  isExact,
  groundInstances,
  ctorNames,
}:
let
  inherit (builtins)
    attrNames
    concatMap
    elem
    filter
    foldl'
    isAttrs
    isString
    sort
    toJSON
    ;
  tm = T.term;
  who = "gen-program.instanceDeclarations";
  isRefusal = v: isAttrs v && (v.refused or false) == true;

  digestOf =
    t:
    let
      i = identityOf t;
    in
    if isExact i then i.minted else null;

  # A body's identity: its clauses' rule identities, as a set (clause order is not identity).
  bodyDigest =
    b:
    let
      ds = map (c: (c.__mint or { }).minted or null) b.clauses;
    in
    if elem null ds then
      null
    else
      hashIdentity "instance-body" [ "clauses" ] (_: sort (x: y: x < y) ds);

  checkApplication =
    a:
    prelude.checkOptions who [ "body" "context" "at" "when" "sources" "door" ] (
      prelude.checkRequired who [ "body" "context" "at" "when" ] a
    );

  # FIRING identity: the firing's own mint (the rule identity, which carries the constructor and the
  # kind, plus the read sources), qualified by what the interpreter cannot see: the policy and the
  # application's context identifier.
  firingId =
    app: d:
    let
      m = d.__mint or null;
    in
    if !(elem d.ctor ctorNames) then
      throw "${who}: a firing of '${app.body.name}' at '${app.at}' carries the constructor '${toString d.ctor}', which is not one of ${toString ctorNames}; it is refused, never dropped"
    else if m == null then
      throw "${who}: a '${d.ctor}' firing of '${app.body.name}' at '${app.at}' carries no identity (no `__mint`): a door's output is identified by the door's contract, and until it is, the firing is refused rather than keyed by position"
    else if !(m ? minted) then
      throw "${who}: a '${d.ctor}' firing of '${app.body.name}' at '${app.at}' has no identity (${m.unmintable or "unmintable"}); give every read coordinate a source"
    else
      hashIdentity "instance-firing" [ "policy" "at" "firing" ] (
        l:
        {
          policy = app.body.name;
          inherit (app) at;
          firing = m.minted;
        }
        .${l}
      );

  ruleBridge =
    names: applications:
    let
      apps = map checkApplication applications;
      # Each application fires once; a refusal from the interpreter is returned unchanged.
      fired = map (
        a:
        let
          a' =
            if !(isString a.at) then
              throw "${who}: `at` is a ${builtins.typeOf a.at}, expected a context identifier (a string)"
            else
              a;
          r = groundInstances (
            { sources = a.sources or { }; } // (if a ? door then { inherit (a) door; } else { })
          ) a.context a.body;
          # The abnormality defeating a firing is its application's (the policy at `at`), so it is
          # named, and the guard built, once per application rather than once per firing.
          self = ab a'.body.name a'.at;
          guard = tm.all [
            a'.when
            (tm.not (tm.has self.head))
          ];
        in
        {
          app = a';
          inherit r self guard;
        }
      ) apps;
      refusals = filter (x: isRefusal x.r) fired;

      # ── APPLICATION and BODY collisions ──
      appKey =
        x:
        toJSON [
          x.app.body.name
          x.app.at
        ];
      byApp = builtins.all (
        g:
        builtins.length g == 1
        || throw "${who}: '${(builtins.head g).app.body.name}' is applied twice at '${(builtins.head g).app.at}'; an application is identified by its policy and its context identifier, and two presentations of one are refused because nothing shows them to be one without comparing context values"
      ) (builtins.attrValues (builtins.groupBy appKey fired));
      byName = builtins.all (
        g:
        let
          n = (builtins.head g).app.body.name;
          ds = prelude.unique (map (x: bodyDigest x.app.body) g);
        in
        builtins.length g == 1
        || (
          if elem null ds then
            throw "${who}: two applications name the policy '${n}' and a clause of one has no identity, so they cannot be shown to be one body"
          else
            builtins.length ds == 1
            || throw "${who}: two different bodies are named '${n}' (${builtins.concatStringsSep " and " ds}); a suppress target names a policy, so the name must identify one body"
        )
      ) (builtins.attrValues (builtins.groupBy (x: x.app.body.name) fired));

      # ── FIRINGS, keyed by identity ──
      views = concatMap (
        x:
        map (
          d:
          let
            id = firingId x.app d;
          in
          {
            inherit id x;
            view = (removeAttrs d [ "__mint" ]) // {
              policy = x.app.body.name;
              inherit (x.app) at;
              firing = id;
            };
          }
        ) x.r
      ) fired;
      # An identity carries its policy and context identifier, and those are unique per application
      # (above), so a repeated identity comes from ONE application: one computation repeated (same
      # terms, same context). It collapses.
      firings = builtins.mapAttrs (_: builtins.head) (builtins.groupBy (f: f.id) views);
      ids = attrNames firings;

      # A namer's result is closed: a field the bridge would overwrite (`when`) or drop is refused.
      ab =
        policy: at:
        prelude.checkOptions "${who}: the `abnormal` namer's result" [ "head" "relata" ] (
          names.abnormal { inherit policy at; }
        );
      factOf =
        view:
        prelude.checkOptions "${who}: the `fact` namer's result" [ "head" "relata" "label" "promote" ] (
          names.fact view
        );
      declOf =
        f:
        if f.view.ctor == "suppress" then
          let
            a = ab f.view.target f.view.at;
          in
          {
            inherit (a) head relata;
            when = f.x.guard;
          }
        else
          (factOf f.view) // { when = f.x.guard; };
      # One declaration per firing identity, shared by the declarations, the fact checks and the
      # firings' heads.
      decls = builtins.mapAttrs (_: declOf) firings;

      # ── FACT collisions: one atom is one fact (ADR-0020) ──
      abHeads = builtins.listToAttrs (
        concatMap (
          id:
          let
            f = firings.${id};
            v = f.view;
          in
          map (h: {
            name = h;
            value = true;
          }) ([ f.x.self.head ] ++ (if v.ctor == "suppress" then [ (ab v.target v.at).head ] else [ ]))
        ) ids
      );
      shapeOf =
        id:
        let
          v = firings.${id}.view;
          d = decls.${id};
        in
        if v.ctor == "suppress" then
          toJSON {
            ctor = "abnormal";
            inherit (d) relata;
          }
        else
          toJSON {
            inherit (v) ctor;
            kind = v.kind or null;
            inherit (d) relata;
            label = d.label or null;
            promote = d.promote or null;
          };
      byHead =
        builtins.all
          (
            g:
            let
              x = builtins.head g;
              h = decls.${x}.head;
              v = firings.${x}.view;
              shapes = prelude.unique (map shapeOf g);
              bad = filter (y: firings.${y}.view.ctor != "suppress") g;
            in
            (
              isString h
              || throw "${who}: a namer returned a ${builtins.typeOf h} head for the '${v.ctor}' firing ${x}; an atom is a string the caller names"
            )
            && (
              bad == [ ]
              || !(abHeads ? ${h})
              || throw "${who}: '${h}' is named both as the fact of the '${
                firings.${builtins.head bad}.view.ctor
              }' firing ${builtins.head bad} of '${firings.${builtins.head bad}.view.policy}' at '${
                firings.${builtins.head bad}.view.at
              }' and as an abnormality; one atom is one fact"
            )
            && (
              builtins.length shapes == 1
              || throw "${who}: '${h}' names two different facts: ${builtins.concatStringsSep " and " shapes}, from the firings ${builtins.concatStringsSep ", " g}"
            )
          )
          (
            builtins.attrValues (
              builtins.groupBy (
                id:
                let
                  h = decls.${id}.head;
                in
                if isString h then h else ""
              ) ids
            )
          );
    in
    if refusals != [ ] then
      (builtins.head refusals).r
    else
      builtins.seq byApp (
        builtins.seq byName (
          builtins.seq byHead {
            declarations = builtins.attrValues decls;
            firings = builtins.mapAttrs (id: f: f.view // { head = decls.${id}.head; }) firings;
          }
        )
      );
in
{
  # A keyed record (den-hoag-7gp66 P2): two configuration operands with no natural order, every field
  # required, and open (R5), as `body` and `model` are.
  instanceDeclarations = prelude.door {
    name = who;
    required = [
      "fact"
      "abnormal"
    ];
    open = true;
  } ruleBridge;
}
