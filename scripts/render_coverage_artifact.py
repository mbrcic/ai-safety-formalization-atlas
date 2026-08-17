"""Render the source-coverage audit as a standalone HTML page.

The audit is the record; this is the view. They were maintained separately for
three revisions and drifted by eighteen `Yes` rows, because nothing regenerated
the page when the markdown changed. Now the page is derived, so the only way to
change it is to change the audit.

Usage:  python3 scripts/render_coverage_artifact.py [output.html]
        python3 scripts/render_coverage_artifact.py --check
"""

from __future__ import annotations

import html
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
AUDIT = ROOT / "docs" / "provenance" / "source-coverage-audit.md"
DEFAULT_OUT = ROOT / "docs" / "status" / "coverage-audit.html"

CHIP = {
    "Yes": "c-full", "Partial": "c-partial", "No": "c-absent",
    "Beyond": "c-beyond", "Wider": "c-plain", "Same": "c-plain",
    "Narrower": "c-plain", "Mixed": "c-partial", "—": "c-plain", "-": "c-plain",
}


def inline(md: str) -> str:
    """Markdown inline formatting to HTML, escaping everything else."""
    out = html.escape(md.replace(r"\|", "|"))
    out = re.sub(r"`([^`]+)`", r"<code>\1</code>", out)
    out = re.sub(r"\*\*([^*]+)\*\*", r"<b>\1</b>", out)
    out = re.sub(r"(?<!\*)\*([^*]+)\*(?!\*)", r"<em>\1</em>", out)
    out = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", r"\1", out)
    return out


def split_row(line: str) -> list[str]:
    masked = line.replace(r"\|", "\x00")
    return [c.replace("\x00", r"\|").strip() for c in masked.split("|")[1:-1]]


def chip(text: str) -> str:
    bare = text.replace("*", "").strip()
    return f'<span class="chip {CHIP.get(bare, "c-plain")}">{html.escape(bare)}</span>'


def render_blocks(lines: list[str]) -> str:
    """Turn a run of markdown into paragraphs, tables and lists."""
    out: list[str] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("|"):
            rows = []
            while i < len(lines) and lines[i].startswith("|"):
                rows.append(split_row(lines[i]))
                i += 1
            is_sep = lambda r: all(set(c) <= {"-", ":"} for c in r if c)
            has_header = len(rows) > 1 and is_sep(rows[1])
            rows = [r for r in rows if not is_sep(r)]
            if not rows:
                continue
            # a run with no separator line is a stray continuation of the table
            # above, not a table with its first row as the header
            head, body = (rows[0], rows[1:]) if has_header else ([], rows)
            ncol = len(head) if head else (len(body[0]) if body else 0)
            out.append('<div class="scroller"><table>')
            if head:
                out.append("<thead><tr>" + "".join(f"<th>{inline(c)}</th>" for c in head)
                           + "</tr></thead>")
            out.append("<tbody>")
            for r in body:
                cells = []
                for j, c in enumerate(r):
                    if ncol == 6 and j in (3, 4):
                        cells.append(f"<td>{chip(c)}</td>")
                    elif ncol == 6 and j == 0:
                        cells.append(f'<td class="src">{inline(c)}</td>')
                    elif ncol == 6 and j == 2:
                        cells.append(f'<td class="decl">{inline(c)}</td>')
                    elif ncol == 6 and j == 5:
                        cells.append(f'<td class="note">{inline(c)}</td>')
                    else:
                        cells.append(f"<td>{inline(c)}</td>")
                out.append("<tr>" + "".join(cells) + "</tr>")
            out.append("</tbody></table></div>")
            continue
        if line.startswith(("* ", "- ")) or re.match(r"^\d+\. ", line):
            ordered = bool(re.match(r"^\d+\. ", line))
            tag = "ol" if ordered else "ul"
            items: list[str] = []
            while i < len(lines) and (
                lines[i].startswith(("* ", "- "))
                or re.match(r"^\d+\. ", lines[i])
                or (items and lines[i].startswith("  ") and lines[i].strip())
            ):
                cur = lines[i]
                if cur.startswith(("* ", "- ")) or re.match(r"^\d+\. ", cur):
                    items.append(re.sub(r"^(?:[*-] |\d+\. )", "", cur))
                else:
                    items[-1] += " " + cur.strip()
                i += 1
            out.append(f"<{tag}>" + "".join(f"<li>{inline(x)}</li>" for x in items) + f"</{tag}>")
            continue
        if not line.strip():
            i += 1
            continue
        para: list[str] = []
        while i < len(lines) and lines[i].strip() and not lines[i].startswith(("|", "* ", "- ", "#")):
            para.append(lines[i])
            i += 1
        text = " ".join(para)
        cls = "verdict" if text.lstrip().startswith("**") else "lede"
        out.append(f'<p class="{cls}">{inline(text)}</p>')
    return "\n".join(out)


def main() -> int:
    md = AUDIT.read_text()
    args = [a for a in sys.argv[1:] if a != "--check"]
    check = "--check" in sys.argv[1:]
    # An unrecognized flag must not be taken as an output path, or a typo writes a
    # file literally named `--write` and left the artifact stale.
    unknown = [a for a in args if a.startswith("-")]
    if unknown:
        print(f"render_coverage_artifact: unknown option(s) {' '.join(unknown)}; "
              "usage: render_coverage_artifact.py [--check] [OUT_PATH]", file=sys.stderr)
        return 2
    if len(args) > 1:
        print("render_coverage_artifact: at most one output path", file=sys.stderr)
        return 2
    out_path = Path(args[0]) if args else DEFAULT_OUT

    lines = md.split("\n")
    # split on `## ` headings
    chunks: list[tuple[str | None, list[str]]] = []
    current: tuple[str | None, list[str]] = (None, [])
    for line in lines:
        if line.startswith("## "):
            chunks.append(current)
            current = (line[3:].strip(), [])
        elif line.startswith("# "):
            continue
        else:
            current[1].append(line)
    chunks.append(current)

    totals = None
    for name, body in chunks:
        if name == "Totals":
            for line in body:
                m = re.match(r"^\| \*\*total\*\* \| \*\*(\d+)\*\* \| \*\*(\d+)\*\* \| \*\*(\d+)\*\* \| \*\*(\d+)\*\* \|", line)
                if m:
                    totals = tuple(int(x) for x in m.groups())
    if totals is None:
        raise SystemExit("render_coverage_artifact: no grand-total row in the audit")

    body_html: list[str] = []
    # the header's source count is derived, not typed: an earlier revision kept
    # saying "six sources" after one was removed from the audit
    source_sections = 0
    for name, block in chunks:
        if name is None:
            body_html.append('<div class="legend-block">' + render_blocks(block) + "</div>")
            continue
        m = re.match(r"^(\d+)\.\s*(.+)$", name)
        if m:
            source_sections += 1
            num, title = m.group(1).zfill(2), m.group(2)
            target = ""
            tm = re.search(r"→\s*`([^`]+)`", title)
            if tm:
                target = f'<p class="target">→ <code>{html.escape(tm.group(1))}</code></p>'
                title = title[: tm.start()].strip().rstrip("→").strip()
            body_html.append(
                f'<section><div class="shead"><span class="snum">{num}</span>'
                f"<h2>{inline(title)}</h2></div>{target}" + render_blocks(block) + "</section>"
            )
        else:
            body_html.append(
                f'<section><div class="shead"><h2>{inline(name)}</h2></div>'
                + render_blocks(block) + "</section>"
            )

    page = TEMPLATE.format(
        yes=totals[0], partial=totals[1], no=totals[2], beyond=totals[3],
        sources=source_sections,
        body="\n".join(body_html),
    )
    if check:
        if not out_path.exists() or out_path.read_text() != page:
            print(
                "render_coverage_artifact: generated file is out of date: "
                f"{out_path}. Re-run scripts/render_coverage_artifact.py",
                file=sys.stderr,
            )
            return 1
        print(
            f"coverage artifact ok: {out_path.name} matches the audit "
            f"({totals[0]} Yes / {totals[1]} Partial / {totals[2]} No / {totals[3]} Beyond)"
        )
        return 0

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(page)
    try:
        shown = out_path.relative_to(ROOT)
    except ValueError:
        shown = out_path
    print(
        f"coverage artifact written: {shown} "
        f"({totals[0]} Yes / {totals[1]} Partial / {totals[2]} No / {totals[3]} Beyond)"
    )
    return 0


TEMPLATE = """<title>Atlas Source Coverage</title>
<style>
  :root {{
    --ground: #F6F7F9; --surface: #FFFFFF; --surface-2: #EEF0F4;
    --ink: #14161C; --muted: #5C6472; --faint: #8A8F9A; --rule: #DEE1E8;
    --accent: #3A4EA8; --accent-soft: #E8EBF7;
    --full: #1E7A5A; --full-soft: #E3F1EB;
    --partial: #9A6412; --partial-soft: #F7EEDC;
    --absent: #767C88; --absent-soft: #ECEEF1;
    --beyond: #5F44A0; --beyond-soft: #EDE8F7;
    --serif: ui-serif, "Iowan Old Style", "Palatino Linotype", Palatino, Georgia, serif;
    --sans: ui-sans-serif, system-ui, -apple-system, "Segoe UI", Roboto, sans-serif;
    --mono: ui-monospace, "SF Mono", SFMono-Regular, Menlo, Consolas, monospace;
  }}
  @media (prefers-color-scheme: dark) {{
    :root:not([data-theme="light"]) {{
      --ground: #0F1116; --surface: #171A21; --surface-2: #1E222B;
      --ink: #E8EAF0; --muted: #A2A9B8; --faint: #767D8C; --rule: #2A2F3A;
      --accent: #93A4EC; --accent-soft: #1D2440;
      --full: #63C39C; --full-soft: #142A22;
      --partial: #D6A34E; --partial-soft: #2C2314;
      --absent: #8B92A0; --absent-soft: #22262E;
      --beyond: #AC93E8; --beyond-soft: #241E38;
    }}
  }}
  :root[data-theme="dark"] {{
    --ground: #0F1116; --surface: #171A21; --surface-2: #1E222B;
    --ink: #E8EAF0; --muted: #A2A9B8; --faint: #767D8C; --rule: #2A2F3A;
    --accent: #93A4EC; --accent-soft: #1D2440;
    --full: #63C39C; --full-soft: #142A22;
    --partial: #D6A34E; --partial-soft: #2C2314;
    --absent: #8B92A0; --absent-soft: #22262E;
    --beyond: #AC93E8; --beyond-soft: #241E38;
  }}
  * {{ box-sizing: border-box; }}
  body {{ background: var(--ground); color: var(--ink); font-family: var(--sans);
    font-size: 16px; line-height: 1.6; margin: 0; padding: 0 20px 96px;
    -webkit-font-smoothing: antialiased; }}
  .wrap {{ max-width: 1040px; margin: 0 auto; }}
  h1, h2, h3 {{ font-family: var(--serif); text-wrap: balance; font-weight: 600; }}
  header {{ padding: 56px 0 32px; border-bottom: 2px solid var(--ink); margin-bottom: 36px; }}
  .eyebrow {{ font-family: var(--mono); font-size: 11px; letter-spacing: 0.13em;
    text-transform: uppercase; color: var(--accent); margin: 0 0 14px; }}
  h1 {{ font-size: clamp(32px, 5.2vw, 48px); line-height: 1.08; margin: 0 0 16px;
    letter-spacing: -0.015em; }}
  .standfirst {{ font-size: 19px; line-height: 1.55; color: var(--muted);
    max-width: 60ch; margin: 0 0 24px; }}
  .meta {{ display: flex; flex-wrap: wrap; gap: 10px 28px; font-family: var(--mono);
    font-size: 12px; color: var(--faint); }}
  .meta b {{ color: var(--muted); font-weight: 500; }}
  .totals-grid {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(150px, 1fr));
    gap: 1px; background: var(--rule); border: 1px solid var(--rule); margin: 0 0 8px; }}
  .tcell {{ background: var(--surface); padding: 16px 18px; }}
  .tcell .n {{ font-size: 30px; font-variant-numeric: tabular-nums;
    font-family: var(--serif); line-height: 1; }}
  .tcell .lbl {{ font-family: var(--mono); font-size: 10.5px; letter-spacing: 0.1em;
    text-transform: uppercase; color: var(--faint); margin-top: 7px; }}
  .n.full {{ color: var(--full); }} .n.partial {{ color: var(--partial); }}
  .n.absent {{ color: var(--absent); }} .n.beyond {{ color: var(--beyond); }}
  .legend-block {{ margin: 30px 0 0; }}
  .legend-block p {{ color: var(--muted); font-size: 14.5px; max-width: 74ch; }}
  section {{ margin-top: 52px; }}
  .shead {{ display: flex; align-items: baseline; gap: 14px; flex-wrap: wrap; margin-bottom: 6px; }}
  .snum {{ font-family: var(--mono); font-size: 12px; color: var(--accent); letter-spacing: 0.08em; }}
  h2 {{ font-size: 25px; margin: 0; letter-spacing: -0.01em; }}
  .target {{ font-family: var(--mono); font-size: 12.5px; color: var(--muted);
    margin: 2px 0 14px; word-break: break-word; }}
  .lede, .verdict {{ font-size: 15px; margin: 16px 0 0; color: var(--muted); max-width: 74ch; }}
  .verdict b, .lede b {{ color: var(--ink); }}
  ol, ul {{ color: var(--muted); font-size: 15px; max-width: 74ch; padding-left: 20px; }}
  li {{ margin-bottom: 9px; }}
  li b {{ color: var(--ink); }}
  .scroller {{ overflow-x: auto; border: 1px solid var(--rule); background: var(--surface);
    margin-top: 18px; }}
  table {{ border-collapse: collapse; width: 100%; min-width: 780px; font-size: 14px; }}
  th {{ text-align: left; font-family: var(--mono); font-size: 10.5px; letter-spacing: 0.09em;
    text-transform: uppercase; color: var(--faint); font-weight: 500; padding: 11px 14px;
    border-bottom: 1px solid var(--rule); background: var(--surface-2); white-space: nowrap; }}
  td {{ padding: 12px 14px; border-bottom: 1px solid var(--rule); vertical-align: top;
    line-height: 1.45; }}
  tr:last-child td {{ border-bottom: none; }}
  td.src {{ font-family: var(--mono); font-size: 11.5px; color: var(--muted); min-width: 110px; }}
  td.decl {{ font-family: var(--mono); font-size: 11.5px; color: var(--accent);
    min-width: 150px; word-break: break-word; }}
  td.note {{ color: var(--muted); font-size: 13px; min-width: 220px; }}
  code {{ font-family: var(--mono); font-size: 0.9em; background: var(--surface-2);
    padding: 1px 4px; border-radius: 2px; }}
  td.decl code, .target code {{ background: none; padding: 0; }}
  .chip {{ display: inline-block; font-family: var(--mono); font-size: 10.5px;
    letter-spacing: 0.06em; text-transform: uppercase; padding: 3px 8px; border-radius: 2px;
    white-space: nowrap; font-weight: 600; }}
  .c-full {{ background: var(--full-soft); color: var(--full); }}
  .c-partial {{ background: var(--partial-soft); color: var(--partial); }}
  .c-absent {{ background: var(--absent-soft); color: var(--absent); }}
  .c-beyond {{ background: var(--beyond-soft); color: var(--beyond); }}
  .c-plain {{ background: var(--surface-2); color: var(--muted); }}
  a {{ color: var(--accent); }}
  a:focus-visible {{ outline: 2px solid var(--accent); outline-offset: 2px; }}
</style>

<div class="wrap">
<header>
  <p class="eyebrow">Provenance audit</p>
  <h1>Atlas Source Coverage</h1>
  <p class="standfirst">Every statement in the sections of {sources} sources the atlas formalizes from, checked one by one against the Lean — what is covered, and how the mechanized statement compares in generality.</p>
  <div class="meta">
    <span><b>Sources read</b> {sources} of {sources}</span>
    <span><b>Generated from</b> source-coverage-audit.md</span>
  </div>
</header>

<div class="totals-grid">
  <div class="tcell"><div class="n full">{yes}</div><div class="lbl">Covered</div></div>
  <div class="tcell"><div class="n partial">{partial}</div><div class="lbl">Partial</div></div>
  <div class="tcell"><div class="n absent">{no}</div><div class="lbl">Not covered</div></div>
  <div class="tcell"><div class="n beyond">{beyond}</div><div class="lbl">Beyond source</div></div>
</div>

{body}
</div>
"""


if __name__ == "__main__":
    raise SystemExit(main())
