"""Build html/euclidean_metric_review.html: a self-contained review page
(figures embedded as base64, agent notes rendered from discussion/*.md).

Usage:  python build_review.py
"""
import base64
import html
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parent.parent
FIG, DISC, OUT = ROOT / "figures", ROOT / "discussion", ROOT / "html" / "euclidean_metric_review.html"

NOTES = [(f"{a}_round{r}.md", f"{a} · {who} · round {r}")
         for a, who in [("P", "Theorist"), ("Q", "Experimenter"), ("R", "Data analyst"), ("S", "Literature")]
         for r in (1, 2)]

tpl = (pathlib.Path(__file__).parent / "review_template.html").read_text()
tpl = re.sub(r"\{\{IMG:([^}]+)\}\}",
             lambda m: "data:image/png;base64," + base64.b64encode((FIG / m.group(1)).read_bytes()).decode(), tpl)
md = {f: (DISC / f).read_text() for f, _ in NOTES}
notes = "\n".join(
    f'<details class="wu"><summary>{html.escape(t)}</summary>'
    f'<div class="md" data-src="{f}"><pre>{html.escape(md[f])}</pre></div></details>' for f, t in NOTES)
page = tpl.replace("{{NOTES}}", notes).replace("{{MD_JSON}}", json.dumps(md).replace("</", "<\\/"))
OUT.write_text(page)
print(OUT, f"{OUT.stat().st_size / 1e6:.2f} MB")
