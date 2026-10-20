#!/usr/bin/env python3
"""Index a problem tree into SQLite, optionally export it as RDF Turtle, and run saved queries.

usage: index.py DIR [--db PATH] [--ttl PATH|-] [--base IRI] [-q NAME [ARG]]

DIR is a project's problems/ folder. The Markdown stays the source of truth: the database is
rebuilt from it on every run and may be deleted at any time (SPEC §20). Story points in
storyline/ and briefs in briefs/ beside problems/ are indexed too. PyYAML only.
"""
import argparse
import datetime
import pathlib
import re
import sqlite3
import sys
from collections import defaultdict
from urllib.parse import quote

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from validate import _artifacts, label, load, rollup  # noqa: E402

import yaml  # noqa: E402  (validate.py has already checked it is installed)

WIKI_LINK = re.compile(r"(?<!!)\[\[([^\]|#]+)(?:#[^\]|]*)?(?:\|([^\]]*))?\]\]")  # as in serve.py
PR = re.compile(r"([\w.-]+)#(\d+)")
COMMIT = re.compile(r"(?:([\w.-]+)@)?([0-9a-f]{7,40})")
DATE = re.compile(r"\d{4}-\d\d-\d\d")
UNRESOLVED = ("open", "fix-proposed", "fix-landed")

SCHEMA = """
CREATE TABLE nodes (id TEXT PRIMARY KEY, type TEXT, title TEXT, status TEXT, resolution TEXT,
  parent TEXT, discovered_from TEXT, promoted_to TEXT, category TEXT, assignee TEXT, source TEXT,
  opened TEXT, closed TEXT, instrument TEXT, todo TEXT, revisit TEXT, rollup TEXT, path TEXT, body TEXT);
CREATE TABLE aliases (alias TEXT PRIMARY KEY, id TEXT);
CREATE TABLE tags (id TEXT, tag TEXT);
-- node -> node or note. kind: parent | discovered_from | promoted_to | member | wikilink.
-- dst is a node id when dst_node = 1 (aliases resolved), else the wikilink target as written.
CREATE TABLE edges (src TEXT, dst TEXT, kind TEXT, dst_node INTEGER);
CREATE TABLE members (sprint TEXT, id TEXT, rank INTEGER, priority TEXT, owner TEXT);
-- role: before | after | artifact (the legacy single path). path is relative to the project folder.
CREATE TABLE evidence (id TEXT, role TEXT, idx INTEGER, artifact TEXT, path TEXT, present INTEGER,
  data TEXT, repo TEXT, commit_ TEXT, branch TEXT, job TEXT, note TEXT);
-- kind: pr | commit | config | note | ...; ref is repo#n or repo@sha as written.
CREATE TABLE fixes (id TEXT, idx INTEGER, kind TEXT, repo TEXT, ref TEXT);
CREATE TABLE sessions (id TEXT, harness TEXT, ref TEXT);
CREATE TABLE stories (slug TEXT PRIMARY KEY, date TEXT, title TEXT, kind TEXT, answers TEXT, path TEXT, summary TEXT);
CREATE TABLE story_nodes (slug TEXT, id TEXT);
CREATE TABLE story_figures (slug TEXT, role TEXT, path TEXT, caption TEXT);
CREATE TABLE briefs (node TEXT, parent_node TEXT, parent_session TEXT, written TEXT, path TEXT);
CREATE TABLE meta (key TEXT PRIMARY KEY, value TEXT);
"""

# Saved queries: name -> (help, SQL). :arg is the query's one argument, aliases resolved to ids.
QUERIES = {
    "summary": ("nodes by type and status", """
        SELECT type, status, count(*) AS n FROM nodes GROUP BY type, status ORDER BY type, n DESC"""),
    "open": ("unresolved leaf work, oldest first, with before/after evidence counts", """
        SELECT n.id, n.type, n.status, n.opened,
          (SELECT count(*) FROM evidence e WHERE e.id = n.id AND e.role = 'before') AS before,
          (SELECT count(*) FROM evidence e WHERE e.id = n.id AND e.role != 'before') AS after, n.title
        FROM nodes n
        WHERE n.status IN ('open', 'fix-proposed', 'fix-landed')
          AND NOT EXISTS (SELECT 1 FROM nodes c WHERE c.parent = n.id AND c.type != 'observation')
        ORDER BY n.opened, n.id"""),
    "lineage": ("ARG and its ancestors up to the root", """
        WITH RECURSIVE up(id, depth) AS (
          SELECT :arg, 0 UNION ALL
          SELECT n.parent, up.depth + 1 FROM up JOIN nodes n ON n.id = up.id WHERE n.parent IS NOT NULL)
        SELECT up.depth, n.id, n.type, n.status, n.title FROM up JOIN nodes n USING (id) ORDER BY up.depth"""),
    "subtree": ("ARG and everything under it", """
        WITH RECURSIVE down(id, depth, trail) AS (
          SELECT :arg, 0, :arg UNION ALL
          SELECT n.id, d.depth + 1, d.trail || '/' || n.id FROM down d JOIN nodes n ON n.parent = d.id)
        SELECT d.depth, n.id, n.type, n.status, n.title FROM down d JOIN nodes n USING (id) ORDER BY d.trail"""),
    "surfaced": ("nodes whose work surfaced others (discovered_from), with the count, direct and transitive", """
        WITH RECURSIVE s(root, id) AS (
          SELECT discovered_from, id FROM nodes WHERE discovered_from IS NOT NULL UNION
          SELECT s.root, n.id FROM s JOIN nodes n ON n.discovered_from = s.id)
        SELECT root AS id, (SELECT count(*) FROM nodes WHERE discovered_from = root) AS direct,
          count(*) AS transitive, (SELECT title FROM nodes WHERE id = root) AS title
        FROM s GROUP BY root ORDER BY transitive DESC"""),
    "durations": ("closed nodes by days from opened to closed, longest first", """
        SELECT id, type, status, opened, closed,
          CAST(julianday(closed) - julianday(opened) AS INTEGER) AS days, title
        FROM nodes WHERE closed IS NOT NULL AND opened IS NOT NULL ORDER BY days DESC"""),
    "fixes": ("each PR, commit or config change and the nodes it fixed", """
        SELECT kind, ref, count(*) AS n, group_concat(id, ' ') AS nodes FROM fixes
        GROUP BY kind, ref ORDER BY n DESC, kind, ref"""),
    "shared": ("evidence files cited by more than one node", """
        SELECT path, count(DISTINCT id) AS n, group_concat(DISTINCT id) AS nodes FROM evidence
        WHERE path IS NOT NULL GROUP BY path HAVING n > 1 ORDER BY n DESC"""),
    "stories": ("story points with the nodes they draw on", """
        SELECT s.date, s.slug, sn.id, n.status, s.title FROM stories s
        LEFT JOIN story_nodes sn USING (slug) LEFT JOIN nodes n ON n.id = sn.id ORDER BY s.date"""),
    "search": ("full-text search of titles and bodies for ARG (FTS5 syntax)", """
        SELECT n.id, n.type, n.status, n.title FROM nodes_fts f JOIN nodes n ON n.id = f.id
        WHERE nodes_fts MATCH :arg ORDER BY rank"""),
}


def s(v):
    """YAML scalar -> text for SQLite (dates come back from PyYAML as date objects)."""
    return None if v is None else str(v)


def frontmatter(path):
    text = path.read_text(encoding="utf-8")
    end = text.find("\n---", 4)
    if not text.startswith("---\n") or end < 0:
        return None, ""
    try:
        fm = yaml.safe_load(text[4:end])
    except yaml.YAMLError:
        return None, ""
    return (fm if isinstance(fm, dict) else None), text[end + 4:]


def entries(v):
    """A frontmatter list of evidence or fix entries, with bare strings as {artifact|note: str}."""
    return [e for e in (v or []) if isinstance(e, (dict, str))]


def build(root, db_path):
    """Read the tree at `root` and (re)write the database at `db_path`. Returns the open connection."""
    root = pathlib.Path(root).resolve()
    project = root.parent
    nodes, errors = load(root)
    for who, msg in errors:
        print(f"skipped {who}: {msg}", file=sys.stderr)
    byid = {n["id"]: n for n in nodes}
    alias = {a: n["id"] for n in nodes for a in n.get("aliases") or []}
    ref = lambda x: x if x in byid else alias.get(x)  # noqa: E731
    children = defaultdict(list)
    for n in nodes:
        children[n.get("parent")].append(n["id"])
    rolled = rollup(byid, children)

    db_path = pathlib.Path(db_path).expanduser()
    db_path.parent.mkdir(parents=True, exist_ok=True)
    db_path.unlink(missing_ok=True)
    con = sqlite3.connect(db_path)
    con.executescript(SCHEMA)
    q = con.execute
    for n in nodes:
        i = n["id"]
        q("INSERT INTO nodes VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)", (
            i, n.get("type"), s(n.get("title")), n.get("status"), n.get("resolution"), n.get("parent"),
            n.get("discovered_from"), n.get("promoted_to"), s(n.get("category")), s(n.get("assignee")),
            n.get("source"), s(n.get("opened")), s(n.get("closed")), s(n.get("instrument")), s(n.get("todo")),
            s(n.get("revisit")), label(rolled[i]) if children.get(i) else None,
            str(n["_path"].relative_to(project)), n["_body"]))
        for a in n.get("aliases") or []:
            q("INSERT OR IGNORE INTO aliases VALUES (?,?)", (s(a), i))
        for t in n.get("tags") or []:
            q("INSERT INTO tags VALUES (?,?)", (i, s(t)))
        for kind in ("parent", "discovered_from", "promoted_to"):
            if n.get(kind) is not None:
                q("INSERT INTO edges VALUES (?,?,?,?)", (i, ref(n[kind]) or s(n[kind]), kind, ref(n[kind]) is not None))
        for target in {m.group(1).strip() for m in WIKI_LINK.finditer(n["_body"])}:
            q("INSERT INTO edges VALUES (?,?,?,?)", (i, ref(target) or target, "wikilink", ref(target) is not None))
        for rank, m in enumerate(n.get("members") or [], 1):
            if isinstance(m, dict) and m.get("id"):
                mid = ref(m["id"]) or s(m["id"])
                q("INSERT INTO members VALUES (?,?,?,?,?)", (i, mid, rank, m.get("priority"), s(m.get("owner"))))
                q("INSERT INTO edges VALUES (?,?,?,?)", (i, mid, "member", mid in byid))
        _evidence(q, n, project)
        for k, e in enumerate(entries(n.get("fix"))):
            e = {"note": e} if isinstance(e, str) else e
            for kind, v in e.items():
                m = PR.fullmatch(str(v)) if kind == "pr" else COMMIT.fullmatch(str(v)) if kind == "commit" else None
                q("INSERT INTO fixes VALUES (?,?,?,?,?)", (i, k, kind, m and m.group(1), s(v)))
        for e in n.get("sessions") or []:
            if isinstance(e, dict) and e.get("ref"):
                q("INSERT INTO sessions VALUES (?,?,?)", (i, e.get("harness", "pi"), s(e["ref"])))
    _stories(q, project, ref)
    _briefs(q, project, ref)
    q("INSERT INTO meta VALUES ('root', ?)", (str(root),))
    q("INSERT INTO meta VALUES ('built', ?)", (datetime.datetime.now().isoformat(timespec="seconds"),))
    try:  # full-text search; some SQLite builds lack FTS5, and then only `search` is missing
        q("CREATE VIRTUAL TABLE nodes_fts USING fts5(id UNINDEXED, title, body)")
        q("INSERT INTO nodes_fts SELECT id, title, body FROM nodes")
    except sqlite3.OperationalError:
        pass
    con.commit()
    return con


def _evidence(q, n, project):
    for role in ("before", "after"):
        for k, e in enumerate(entries(n.get(role))):
            e = {"artifact": e} if isinstance(e, str) else e
            path, present = None, None
            if e.get("artifact"):
                p = (n["_path"].parent / str(e["artifact"])).resolve()
                path, present = _rel(p, project), p.exists()
            q("INSERT INTO evidence VALUES (?,?,?,?,?,?,?,?,?,?,?,?)", (
                n["id"], role, k, s(e.get("artifact")), path, present, s(e.get("data")), s(e.get("repo")),
                s(e.get("commit")), s(e.get("branch")), s(e.get("job")), s(e.get("note"))))
    if n.get("artifact"):
        p = (n["_path"].parent / str(n["artifact"])).resolve()
        q("INSERT INTO evidence (id, role, idx, artifact, path, present) VALUES (?,?,?,?,?,?)",
          (n["id"], "artifact", 0, s(n["artifact"]), _rel(p, project), p.exists()))


def _rel(p, project):
    try:
        return str(p.relative_to(project))
    except ValueError:
        return str(p)


def _stories(q, project, ref):
    """SPEC §18: storyline/<slug>.md, type: story."""
    for path in sorted((project / "storyline").glob("*.md")):
        fm, body = frontmatter(path)
        if not fm or fm.get("type") != "story":
            continue
        slug = path.stem
        summary = re.split(r"\n(?:!\[|##)", body.split("\n# ", 1)[-1].split("\n", 1)[-1], maxsplit=1)[0].strip()
        q("INSERT INTO stories VALUES (?,?,?,?,?,?,?)", (slug, s(fm.get("date")), s(fm.get("title")),
          s(fm.get("kind")), s(fm.get("answers")), str(path.relative_to(project)), summary))
        for i in fm.get("nodes") or []:
            q("INSERT INTO story_nodes VALUES (?,?)", (slug, ref(i) or s(i)))
        for f in fm.get("figures") or []:
            if isinstance(f, dict):
                q("INSERT INTO story_figures VALUES (?,?,?,?)", (slug, f.get("role"),
                  _rel((path.parent / str(f.get("path", ""))).resolve(), project), s(f.get("caption"))))


def _briefs(q, project, ref):
    """briefs/<node-id>.md written by the brief skill."""
    for path in sorted((project / "briefs").glob("*.md")):
        fm, _ = frontmatter(path)
        if fm and fm.get("node"):
            q("INSERT INTO briefs VALUES (?,?,?,?,?)", (ref(fm["node"]) or s(fm["node"]),
              fm.get("parent_node") and (ref(fm["parent_node"]) or s(fm["parent_node"])),
              s(fm.get("parent_session")), s(fm.get("written")), str(path.relative_to(project))))


# --------------------------------------------------------------------------- RDF
# The vocabulary is described in vocab.ttl beside this file; it maps pt: terms onto Dublin Core,
# PROV-O and SKOS. Node, story and session IRIs hang off --base.
VOCAB = "urn:problem-tree:vocab#"
PN_LOCAL = re.compile(r"[A-Za-z0-9_](?:[A-Za-z0-9_.-]*[A-Za-z0-9_-])?")


def lit(v):
    t = str(v)
    if DATE.fullmatch(t):
        return f'"{t}"^^xsd:date'
    if isinstance(v, int) and not isinstance(v, bool):
        return t
    t = t.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\r", "\\r").replace("\t", "\\t")
    return f'"{t}"'


def turtle(con, out, base):
    ns = {"node": f"{base}node/", "story": f"{base}story/", "session": f"{base}session/"}

    def iri(kind, local):
        local = str(local)
        return f"{kind}:{local}" if PN_LOCAL.fullmatch(local) else f"<{ns[kind]}{quote(local, safe='')}>"

    def term(scheme, v):
        """A controlled value as a concept in its scheme (vocab.ttl): status open -> pt:status-open."""
        return f"pt:{scheme}-{v}" if PN_LOCAL.fullmatch(str(v)) else lit(v)

    def block(subject, pairs):
        pairs = [(p, o) for p, o in pairs if o]
        out.write(subject + "\n    " + " ;\n    ".join(f"{p} {o}" for p, o in pairs) + " .\n\n")

    def bnode(pairs):
        pairs = [(p, o) for p, o in pairs if o]
        return "[ " + " ; ".join(f"{p} {o}" for p, o in pairs) + " ]"

    rows = lambda sql, *a: con.execute(sql, a).fetchall()  # noqa: E731
    cls = {"problem": "pt:Problem", "task": "pt:Task", "observation": "pt:Observation"}
    out.write(f"# problem tree {rows('SELECT value FROM meta WHERE key = ?', 'root')[0][0]}\n"
              f"# written by index.py; the Markdown is the source of truth. Vocabulary: vocab.ttl\n")
    for p, v in (("pt", VOCAB), *ns.items(), ("dcterms", "http://purl.org/dc/terms/"),
                 ("prov", "http://www.w3.org/ns/prov#"), ("xsd", "http://www.w3.org/2001/XMLSchema#")):
        out.write(f"@prefix {p}: <{v}> .\n")
    out.write("\n")

    for (i, typ, title, status, res, parent, disc, promo, cat, who, src, opened, closed, instr, todo, revisit,
         roll) in rows("SELECT id, type, title, status, resolution, parent, discovered_from, promoted_to, category,"
                       " assignee, source, opened, closed, instrument, todo, revisit, rollup FROM nodes ORDER BY id"):
        pairs = [("a", cls.get(typ, "pt:Node")), ("dcterms:identifier", lit(i)), ("dcterms:title", title and lit(title)),
                 ("pt:status", status and term("status", status)), ("pt:resolution", res and term("resolution", res)),
                 ("pt:rollup", roll and term("rollup", roll)), ("pt:parent", parent and iri("node", parent)),
                 ("pt:discoveredFrom", disc and iri("node", disc)), ("pt:promotedTo", promo and iri("node", promo)),
                 ("pt:category", cat and lit(cat)), ("pt:assignee", who and lit(who)), ("pt:source", src and term("source", src)),
                 ("dcterms:created", opened and lit(opened)), ("pt:closed", closed and lit(closed)),
                 ("pt:instrument", instr and lit(instr)), ("pt:todo", todo and lit(todo)),
                 ("pt:revisit", revisit and lit(revisit))]
        pairs += [("pt:alias", lit(a)) for (a,) in rows("SELECT alias FROM aliases WHERE id = ?", i)]
        pairs += [("dcterms:subject", lit(t)) for (t,) in rows("SELECT tag FROM tags WHERE id = ?", i)]
        pairs += [("dcterms:references", iri("node", d) if is_node else lit(d))
                  for d, is_node in rows("SELECT dst, dst_node FROM edges WHERE src = ? AND kind = 'wikilink'", i)]
        for role, art, path, data, repo, commit, branch, job, note in rows(
                "SELECT role, artifact, path, data, repo, commit_, branch, job, note FROM evidence WHERE id = ?"
                " ORDER BY role, idx", i):
            pairs.append(("pt:" + ("after" if role == "artifact" else role), bnode([
                ("a", "pt:Evidence"), ("pt:artifact", path and lit(path)), ("pt:data", data and lit(data)),
                ("pt:repo", repo and lit(repo)), ("pt:commit", commit and lit(commit)),
                ("pt:branch", branch and lit(branch)), ("pt:job", job and lit(job)), ("pt:note", note and lit(note))])))
        for k in sorted({k for (k,) in rows("SELECT idx FROM fixes WHERE id = ?", i)}):
            pairs.append(("pt:fix", bnode([("a", "pt:Fix")] + [
                ("pt:" + (kind if PN_LOCAL.fullmatch(kind) else "note"), lit(r))
                for kind, r in rows("SELECT kind, ref FROM fixes WHERE id = ? AND idx = ?", i, k)])))
        for rank, mid, prio, owner in rows("SELECT rank, id, priority, owner FROM members WHERE sprint = ? ORDER BY rank", i):
            pairs.append(("pt:member", bnode([("a", "pt:Membership"), ("pt:node", iri("node", mid)), ("pt:rank", lit(rank)),
                                              ("pt:priority", prio and lit(prio)), ("pt:owner", owner and lit(owner))])))
        pairs += [("pt:session", iri("session", r)) for (r,) in rows("SELECT ref FROM sessions WHERE id = ?", i)]
        block(iri("node", i), pairs)

    for harness, r in rows("SELECT DISTINCT harness, ref FROM sessions ORDER BY ref"):
        block(iri("session", r), [("a", "pt:Session"), ("pt:harness", lit(harness)), ("pt:ref", lit(r))])

    for slug, date, title, kind, answers, summary in rows(
            "SELECT slug, date, title, kind, answers, summary FROM stories ORDER BY date, slug"):
        pairs = [("a", "pt:StoryPoint"), ("dcterms:title", title and lit(title)), ("dcterms:date", date and lit(date)),
                 ("pt:kind", kind and term("kind", kind)), ("pt:answers", answers and iri("story", answers)),
                 ("dcterms:description", summary and lit(summary))]
        pairs += [("pt:about", iri("node", n)) for (n,) in rows("SELECT id FROM story_nodes WHERE slug = ?", slug)]
        pairs += [("pt:figure", bnode([("a", "pt:Figure"), ("pt:role", role and term("role", role)), ("pt:artifact", lit(p)),
                                       ("pt:caption", cap and lit(cap))]))
                  for role, p, cap in rows("SELECT role, path, caption FROM story_figures WHERE slug = ?", slug)]
        block(iri("story", slug), pairs)

    for node, pnode, psession, written, path in rows("SELECT * FROM briefs ORDER BY node"):
        block(f"<{ns['node']}{quote(node, safe='')}/brief>", [
            ("a", "pt:Brief"), ("pt:briefFor", iri("node", node)), ("pt:parentNode", pnode and iri("node", pnode)),
            ("pt:parentSession", psession and iri("session", psession)), ("dcterms:created", written and lit(written)),
            ("pt:artifact", lit(path))])


# --------------------------------------------------------------------------- queries
def run_query(con, name, arg):
    help_, sql = QUERIES[name]
    if ":arg" in sql:
        if arg is None:
            sys.exit(f"query {name} needs an argument: {help_}")
        if name != "search":
            arg = (con.execute("SELECT id FROM aliases WHERE alias = ?", (arg,)).fetchone() or (arg,))[0]
    try:
        cur = con.execute(sql, {"arg": arg} if ":arg" in sql else {})
    except sqlite3.OperationalError as exc:
        sys.exit(f"query {name}: {exc}")
    head = [d[0] for d in cur.description]
    rows = [["" if v is None else " ".join(str(v).split()) for v in r] for r in cur.fetchall()]
    rows = [[v if len(v) <= 72 else v[:69] + "…" for v in r] for r in rows]
    width = [max(len(h), *(len(r[k]) for r in rows)) if rows else len(h) for k, h in enumerate(head)]
    for r in [head, *rows]:
        print("  ".join(v.ljust(w) for v, w in zip(r, width)).rstrip())
    print(f"\n{len(rows)} rows")


def main():
    names = "\n".join(f"  {k:<10} {v[0]}" for k, v in QUERIES.items())
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0], epilog="saved queries:\n" + names,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("dir", help="a project's problems/ folder")
    ap.add_argument("--db", help="database file (default ~/.cache/problem-tree/<root id>.db)")
    ap.add_argument("--ttl", help="also write the tree as RDF Turtle to this file, or - for stdout")
    ap.add_argument("--base", default="urn:problem-tree:", help="IRI base for nodes, stories and sessions")
    ap.add_argument("-q", "--query", nargs="+", metavar=("NAME", "ARG"), help="run a saved query after indexing")
    args = ap.parse_args()
    if args.query and (args.query[0] not in QUERIES or len(args.query) > 2):
        ap.error(f"query is NAME [ARG], NAME one of: {', '.join(QUERIES)}")

    db = args.db
    if db is None:
        roots = [n["id"] for n in load(args.dir)[0] if n.get("parent") is None]
        db = f"~/.cache/problem-tree/{roots[0] if len(roots) == 1 else pathlib.Path(args.dir).resolve().parent.name}.db"
    con = build(args.dir, db)
    if args.ttl == "-":
        turtle(con, sys.stdout, args.base)
    elif args.ttl:
        with open(args.ttl, "w", encoding="utf-8") as f:
            turtle(con, f, args.base)
    if args.query:
        run_query(con, args.query[0], args.query[1] if len(args.query) > 1 else None)
    elif args.ttl != "-":
        counts = {t: con.execute(f"SELECT count(*) FROM {t}").fetchone()[0]
                  for t in ("nodes", "edges", "evidence", "fixes", "sessions", "stories", "briefs")}
        print(f"{pathlib.Path(db).expanduser()}: " + ", ".join(f"{v} {k}" for k, v in counts.items())
              + (f"; turtle at {args.ttl}" if args.ttl else ""))


if __name__ == "__main__":
    main()
