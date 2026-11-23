#!/usr/bin/env python3
"""Daily arXiv digest for robertcrumplin.com.

Reads the day's arXiv announcements (RSS), keeps the papers that score highly against the topics
and authors below, and writes them to an unlisted page, OUT/index.html (data kept in OUT/digest.json).
Run every morning by .github/workflows/arxiv-digest.yml; it can also be run by hand:
    python .github/arxiv_digest.py            (reads the live feed)
    python .github/arxiv_digest.py feed.xml   (reads a saved copy of the feed)

To tune what gets picked up, edit TOPICS, AUTHORS, STUDENTS and THRESHOLD.
"""
import datetime as dt
import email.utils
import html
import json
import pathlib
import re
import sys
import unicodedata
import urllib.request
import xml.etree.ElementTree as ET

# ---------------------------------------------------------------------------------------------
# Settings
# ---------------------------------------------------------------------------------------------
FEED = 'https://rss.arxiv.org/rss/math.AG+math.SG+math.CO+math.GT+hep-th'
OUT = pathlib.Path(__file__).resolve().parent.parent / 'arxiv-1bhec9p544'
KEEP_DAYS = 60              # how many announcement days the page keeps
THRESHOLD = 4               # a paper is listed if its score reaches this…
HOME = ('math.AG', 'math.SG')  # …and if its primary category is not one of these, it needs THRESHOLD + 3
INCLUDE = {'new', 'cross'}  # announcement types to consider (also possible: 'replace', 'replace-cross')

# (regular expression, weight). Matched against the lower-cased title and abstract, after LaTeX
# commands such as \overline, \mathcal and the symbols $ { } \ have been removed, and dashes unified.
# A topic found in the title counts double. Each topic counts once however often it appears.
TOPICS = [
    # enumerative geometry and Gromov–Witten theory
    (r'gromov-witten', 4), (r'enumerative(?! combinatori)', 3), (r'curve[- ]counting|counting (rational |holomorphic )?curves|counts? of (rational )?curves', 3),
    (r'stable maps?\b', 3), (r'quasimaps?', 3), (r'virtual (fundamental )?class', 2), (r'(perfect )?obstruction theor', 2),
    (r'double ramification', 3), (r'hurwitz (number|space|cycle|theor)', 2), (r'tautological (ring|class|relation)', 3),
    (r'donaldson-thomas|pandharipande-thomas|gopakumar-vafa', 3), (r'\bbps (state|invariant|count)', 2),
    (r'quantum (cohomology|k-theory|period)', 3), (r'givental|\b[ij]-function', 2), (r'degeneration formula', 3),
    (r'severi variet|welschinger', 2), (r'psi[- ]class|hodge (integral|bundle)|lambda_g', 2),
    # logarithmic and orbifold geometry
    (r'(log|logarithmic) (gromov|stable map|map|curve|geometry|structure|scheme|smooth|modification|blow)', 3),
    (r'punctured (gromov|invariant|map|curve)', 4), (r'artin fan', 3), (r'root stacks?', 3), (r'orbifold (gromov|curve|map)', 3),
    (r'naive (space|theor|invariant)', 2), (r'normal crossings?', 1), (r'snc (pair|divisor)', 2),
    # mirror symmetry and the Gross–Siebert programme
    (r'gross-siebert', 4), (r'mirror symmetry|\bmirrors? (of|for|to|construction|famil)', 3), (r'intrinsic mirror', 4),
    (r'scattering diagram', 4), (r'broken lines?', 3), (r'theta functions?', 1), (r'(log|logarithmic) calabi-yau', 4),
    (r'cluster (variet|algebra|scattering)', 2), (r'toric degeneration', 3), (r'landau-ginzburg', 2),
    (r'strominger-yau-zaslow|\bsyz\b', 3), (r'gamma conjecture', 2), (r'affine (structure|manifold) with singularities', 3),
    (r'wall[- ]crossing', 1),
    # tropical geometry
    (r'tropical (curve|geometry|map|moduli|count|cycle|enumerat|intersection|variet)', 3), (r'tropicali[sz]ation', 3),
    (r'\btropical\b', 1),
    # moduli of curves and maps
    (r'moduli (space|stack)s? of (stable |pointed |prestable |nodal |smooth )*curves', 3), (r'\bm_ ?\(? ?g ?, ?n', 3),
    (r'stable curves?', 2), (r'moduli (space|stack)s? of (stable |logarithmic |log )*maps', 3),
    (r'deligne-mumford', 1), (r'moduli (space|stack)', 1),
    # surroundings
    (r'calabi-yau', 1), (r'del pezzo', 1), (r'\btoric\b', 1), (r'\bfano\b', 1), (r'blow(ing)?[- ]?ups?\b', 1),
    (r'genus[- ](zero|one|0|1|two|g)\b', 1),
]
# People to follow: any paper with one of them as an author is always listed, at the top of its day.
# A name matches an author whole (not as part of a longer name), ignoring accents, case, hyphens and full
# stops; give other spellings after a '|', e.g. 'Tom Graber|Thomas Graber'.
AUTHORS = [
    'Mark Gross', 'Bernd Siebert', 'Paul Hacking', 'Sean Keel', 'Rahul Pandharipande', 'Dhruv Ranganathan',
    'Navid Nabijou', 'Georg Oberdieck', 'Alessio Corti', 'Dan Abramovich', 'Qile Chen', 'Jonathan Wise',
    'Luca Battistella', 'Hsian-Hua Tseng', 'Fenglong You', 'Helge Ruddat', 'Hülya Argüz', 'Pierrick Bousseau',
    'Michel van Garrel', 'Tim Grafnitz', 'Ravi Vakil', 'Aleksey Zinger', 'Sam Johnston', 'Qaasim Shafi',
    'Leo Herr', 'Soham Karwa', 'Davesh Maulik', 'Andrei Okounkov', 'Tom Coates', 'Yongbin Ruan',
]
# PhD students, past and present, of some of the people above; also always listed, marked "student of …".
# Left out because the name is too common to match safely: Yu Wang (Gross), Jianhua Wang and James Spencer
# (Abramovich), Mohammad Akhtar (Corti and Coates).
STUDENTS = {
    'Rahul Pandharipande': [
        'Younghan Bae', 'Benjamin Bakker', 'Ignacio Barros', 'Tim-Henrik Buelles', 'Alessio Cela', 'Yaim Cooper',
        'Tom Graber|Thomas Graber', 'Felix Janda', 'Davesh Maulik', 'Miguel Moreira', 'Georg Oberdieck',
        'Aaron Pixton', 'Christoph Schiessl', 'Johannes Schmitt', 'Iman Setayesh', 'Junliang Shen',
        'Vivek Shende', 'Aitor Iribar López', 'Lycka Drakengren', 'Jeremy Feusi',
    ],
    'Dan Abramovich': [
        'Kenneth Ascher', 'Dori Bejleri', 'Jiun-Cheng Chen', 'Qile Chen', 'Tangli Ge', 'Noah Giansiracusa',
        'Alicia Harper', 'Giovanni Inchiostro', 'Kalle Karu', 'Gabriele La Nave', 'Steffen Marcus',
        'Sam Molcho|Samouil Molcho', 'Patricia Pacelli', 'Ming Hao Quek', 'Evangelos Routis',
        'Henning Úlfarsson', 'Martin Ulirsch', 'Jonathan Wise',
    ],
    'Mark Gross': [
        'Lawrence Barrott|Lawrence Jack Barrott', 'Daniel Budreau', 'Andrei Căldăraru', 'Ricardo Castaño-Bernard',
        'Man-Wai Cheung|Man Wai Cheung|Man-Wai Mandy Cheung', 'Karl Fredrickson', 'Michael Kasa', 'Diego Matessi',
        'Brandon Meredith', 'Peter Overholser', 'Simone Pavanelli', 'Michael Slawinski', 'Xuanchun Lu',
    ],
    'Davesh Maulik': [
        'Chun Hong Lo', 'Svetlana Makarova', 'Tudor Pădurariu', 'Anne Larsen',
    ],
    'Dhruv Ranganathan': [
        'Qaasim Shafi', 'Patrick Kennedy-Hunt', 'Siddarth Kannan', 'Wanlong Zheng', 'Ajith Urundolil Kumaran',
        'Terry Dekun Song|Terry Song|Dekun Song', 'Siao Chi Mok', 'Owen Mackenzie', 'Emily Dodwell',
        'Sae Koyama', 'Ray Shang',
    ],
    'Alessio Corti': [
        'Alessandro Chiodo', 'Giulia Gugiatti', 'Paul Hacking', 'Anne-Sophie Kaloghiros', 'Vladimir Lazić',
        'Andrew Macpherson', 'Andrea Petracci', 'Thomas Prince|Tom Prince', 'Andrew Strangeway',
    ],
    'Tom Coates': [
        'Giulia Gugiatti', 'Elana Kalashnikov', 'Navid Nabijou', 'Thomas Prince|Tom Prince', 'Qaasim Shafi',
        'Andrew Strangeway',
    ],
    'Navid Nabijou': [
        'Cat Rust', 'Dan Simms|Daniel Simms', 'Andy Xiaoan Yang|Xiaoan Yang',
    ],
    # Sam Johnston and Soham Karwa: no students yet.
}
AUTHOR_WEIGHT = 6

# ---------------------------------------------------------------------------------------------
# Reading the feed
# ---------------------------------------------------------------------------------------------
NS = {'dc': 'http://purl.org/dc/elements/1.1/', 'arxiv': 'http://arxiv.org/schemas/atom'}


def plain(s):
    """Accents removed, lower case."""
    return ''.join(c for c in unicodedata.normalize('NFKD', s) if not unicodedata.combining(c)).lower()


def searchable(s):
    s = re.sub(r'\\(mathcal|mathfrak|mathbb|mathrm|mathsf|overline|bar|widetilde|tilde|widehat|hat|operatorname)', '', s)
    s = re.sub(r'[${}\\]', '', s)
    s = s.replace('–', '-').replace('—', '-').replace('--', '-')
    return plain(s)


def read_feed(text):
    root = ET.fromstring(text)
    channel = root.find('channel')
    when = channel.findtext('pubDate') or channel.findtext('lastBuildDate') or ''
    try:
        day = email.utils.parsedate_to_datetime(when).date().isoformat()
    except (TypeError, ValueError):
        day = dt.date.today().isoformat()
    papers = []
    for it in channel.findall('item'):
        desc = it.findtext('description') or ''
        m = re.match(r'\s*arXiv:(\S+?)(v\d+)?\s+Announce Type:\s*(\S+)\s*Abstract:\s*(.*)', desc, re.S)
        if not m:
            continue
        arxiv_id, kind, abstract = m.group(1), m.group(3), m.group(4).strip()
        kind = it.findtext('arxiv:announce_type', default=kind, namespaces=NS) or kind
        papers.append({
            'id': arxiv_id, 'kind': kind,
            'title': ' '.join((it.findtext('title') or '').split()),
            'authors': ' '.join((it.findtext('dc:creator', default='', namespaces=NS) or '').split()),
            'categories': [c.text for c in it.findall('category') if c.text],
            'abstract': ' '.join(abstract.split()),
        })
    return day, papers


# ---------------------------------------------------------------------------------------------
# Scoring
# ---------------------------------------------------------------------------------------------
COMPILED = [(re.compile(p), w, p) for p, w in TOPICS]


def name_key(s):
    """A name with accents, case, hyphens and full stops ignored: 'Jiun-Cheng Chen' -> 'jiun cheng chen'."""
    return ' '.join(re.sub(r'[-.‐–]', ' ', plain(s)).split())


def follow_list():
    """(pattern, advisors) for every followed name and spelling; advisors is empty for people followed directly."""
    found = {}
    for entry in AUTHORS:
        for spelling in entry.split('|'):
            found[name_key(spelling)] = None
    for advisor, students in STUDENTS.items():
        for entry in students:
            for spelling in entry.split('|'):
                key = name_key(spelling)
                if key not in found:
                    found[key] = []
                if found[key] is not None and advisor not in found[key]:
                    found[key].append(advisor)
    return [(re.compile(r'(^| )' + re.escape(k) + r'( |$)'), adv or []) for k, adv in found.items()]


FOLLOWED = follow_list()


def followed_authors(authors):
    """The authors of a paper who are followed, as written in the feed, and a note for each student."""
    people, notes = [], []
    for a in re.split(r',|\band\b', authors):
        a = a.strip()
        key = name_key(a)
        for rx, advisors in FOLLOWED:
            if key and rx.search(key):
                if a not in people:
                    people.append(a)
                    if advisors:
                        notes.append(f'{a} is a student of ' + ' and '.join(x.split()[-1] for x in advisors))
                break
    return people, notes


def score(p):
    title, abstract = searchable(p['title']), searchable(p['abstract'])
    total, hits = 0, []
    for rx, w, pat in COMPILED:
        mt, ma = rx.search(title), rx.search(abstract)
        if mt or ma:
            total += w * (2 if mt else 1)
            hits.append((w * (2 if mt else 1), (mt or ma).group(0)))
    people, notes = followed_authors(p['authors'])
    if people:
        total += AUTHOR_WEIGHT
    if p['categories'] and p['categories'][0] in HOME:
        total += 1
    tags = []
    for _, h in sorted(hits, key=lambda h: -h[0]):
        h = h.strip(' ,(')
        if h not in tags:
            tags.append(h)
    return total, tags[:5], people, notes


# ---------------------------------------------------------------------------------------------
# The page
# ---------------------------------------------------------------------------------------------
def snippet(abstract, limit=420):
    """The first sentences of the abstract, up to about `limit` characters."""
    if len(abstract) <= limit:
        return abstract
    cut = abstract[:limit]
    end = max(cut.rfind('. '), cut.rfind('? '))
    return cut[:end + 1] if end > 120 else cut.rsplit(' ', 1)[0] + ' …'


def render(days, updated):
    e = lambda t: html.escape(t.replace('---', '—').replace('--', '–'))
    out = []
    for d in days:
        nice = dt.date.fromisoformat(d['date']).strftime('%A %-d %B %Y')
        out.append(f'<section><h2>{e(nice)} <span class="count">· {len(d["papers"])} of {d["total"]} announcements</span></h2>')
        if not d['papers']:
            out.append('<p class="none">Nothing close to home today.</p>')
        for p in d['papers']:
            who = e(p['authors'])
            for name in p.get('people', []):
                who = who.replace(e(name), f'<b>{e(name)}</b>')
            if p.get('notes'):
                who += f' <span class="via">· {e("; ".join(p["notes"]))}</span>'
            cats = ' '.join(f'<span class="cat">{e(c)}</span>' for c in p['categories'][:3])
            tags = ' '.join(f'<span class="tag">{e(t)}</span>' for t in p['tags'])
            cross = ' <span class="cross">cross-list</span>' if p['kind'] != 'new' else ''
            out.append(f'''<article>
  <h3><a href="https://arxiv.org/abs/{e(p['id'])}">{e(p['title'])}</a></h3>
  <p class="who">{who}</p>
  <p class="meta"><a href="https://arxiv.org/abs/{e(p['id'])}">arXiv:{e(p['id'])}</a> · <a href="https://arxiv.org/pdf/{e(p['id'])}">pdf</a> · {cats}{cross} · score {p['score']}</p>
  <p class="abs">{e(p['snippet'])}</p>
  <p class="tags">{tags}</p>
</article>''')
        out.append('</section>')
    body = '\n'.join(out) or '<p class="none">No digests yet.</p>'
    return f'''<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="robots" content="noindex, nofollow">
<title>arXiv digest</title>
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.css">
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.js"></script>
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/contrib/auto-render.min.js"
  onload="renderMathInElement(document.body, {{delimiters: [{{left: '$$', right: '$$', display: false}}, {{left: '$', right: '$', display: false}}], throwOnError: false}})"></script>
<style>
  :root {{ --paper: #fbfaf6; --ink: #1c1c1e; --muted: #7a787d; --rule: #dcd8cf; --accent: #b23a1d;
          --serif: "STIX Two Text", "Latin Modern Roman", "Cambria", "Georgia", "Times New Roman", serif; }}
  @media (prefers-color-scheme: dark) {{ :root {{ --paper: #151517; --ink: #ebe9e4; --muted: #9a989d; --rule: #34333a; --accent: #f09a75; }} }}
  html, body {{ margin: 0; background: var(--paper); color: var(--ink); font-family: var(--serif); }}
  main {{ max-width: 46rem; margin: 0 auto; padding: 2.5rem 1.5rem 4rem; line-height: 1.55; }}
  h1 {{ font-weight: 400; font-size: 1.9rem; margin: 0; }}
  .lede {{ color: var(--muted); margin: .3rem 0 0; font-size: .95rem; }}
  .lede a {{ color: inherit; }}
  h2 {{ font-weight: 400; font-size: 1.25rem; margin: 2.4rem 0 .8rem; padding-top: 1rem; border-top: 1px solid var(--rule); }}
  .count {{ color: var(--muted); font-size: .95rem; }}
  article {{ margin: 0 0 1.5rem; }}
  h3 {{ font-weight: 400; font-size: 1.12rem; margin: 0; }}
  h3 a {{ color: inherit; text-decoration-color: var(--rule); text-underline-offset: 3px; }}
  h3 a:hover {{ color: var(--accent); }}
  .who {{ margin: .15rem 0 0; }}
  .who b {{ font-weight: 600; color: var(--accent); }}
  .via {{ color: var(--muted); font-size: .9rem; font-style: italic; }}
  .meta {{ margin: .1rem 0 0; color: var(--muted); font-size: .9rem; }}
  .meta a {{ color: inherit; }}
  .cat {{ white-space: nowrap; }}
  .cross {{ font-style: italic; }}
  .abs {{ margin: .4rem 0 0; font-size: .98rem; }}
  .tags {{ margin: .3rem 0 0; }}
  .tag {{ display: inline-block; font-size: .8rem; color: var(--muted); border: 1px solid var(--rule); border-radius: 999px; padding: 0 .55rem; margin: 0 .25rem .25rem 0; }}
  .none {{ color: var(--muted); font-style: italic; }}
</style>
</head>
<body>
<main>
<h1>arXiv digest</h1>
<p class="lede">New papers and cross-lists in math.AG, math.SG, math.CO, math.GT and hep-th close to enumerative geometry, the
Gross–Siebert programme, mirror symmetry, and moduli of curves and maps, picked from each weekday's arXiv announcements.
Last updated {e(updated)}. Back to <a href="/">robertcrumplin.com</a>.</p>
{body}
</main>
</body>
</html>
'''


# ---------------------------------------------------------------------------------------------
def main():
    if len(sys.argv) > 1:
        text = pathlib.Path(sys.argv[1]).read_text(encoding='utf-8')
    else:
        req = urllib.request.Request(FEED, headers={'User-Agent': 'robertcrumplin.com arXiv digest (once a day)'})
        with urllib.request.urlopen(req, timeout=60) as r:
            text = r.read().decode('utf-8')
    day, papers = read_feed(text)

    OUT.mkdir(parents=True, exist_ok=True)
    store = OUT / 'digest.json'
    data = json.loads(store.read_text(encoding='utf-8')) if store.exists() else {'days': []}
    if any(d['date'] == day for d in data['days']) or not papers:
        print(f'Nothing new: the feed is for {day} ({len(papers)} items), already done or empty.')
        return

    seen = {p['id'] for d in data['days'] for p in d['papers']}
    picked, ids = [], set()
    for p in papers:
        if p['kind'] not in INCLUDE or p['id'] in ids or p['id'] in seen:
            continue
        ids.add(p['id'])
        s, tags, people, notes = score(p)
        need = THRESHOLD if p['categories'] and p['categories'][0] in HOME else THRESHOLD + 3
        if s >= need or people:
            picked.append({**p, 'score': s, 'tags': tags, 'people': people, 'notes': notes,
                           'snippet': snippet(p['abstract'])})
            del picked[-1]['abstract']
    picked.sort(key=lambda p: (-(bool(p['people'])), -p['score']))

    data['days'].insert(0, {'date': day, 'total': len(ids), 'papers': picked})
    data['days'] = sorted(data['days'], key=lambda d: d['date'], reverse=True)[:KEEP_DAYS]
    updated = dt.datetime.now(dt.timezone.utc).strftime('%-d %B %Y, %H:%M UTC')
    store.write_text(json.dumps(data, ensure_ascii=False, indent=1), encoding='utf-8')
    (OUT / 'index.html').write_text(render(data['days'], updated), encoding='utf-8')
    print(f'{day}: listed {len(picked)} of {len(ids)} new papers and cross-lists.')
    for p in picked:
        print(f"  {p['score']:3d}  {p['title'][:90]}  [{', '.join(p['tags'])}]{'  ← ' + ', '.join(p['people']) if p['people'] else ''}")


if __name__ == '__main__':
    main()
