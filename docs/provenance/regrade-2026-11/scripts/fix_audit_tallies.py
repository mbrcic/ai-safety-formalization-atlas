"""Rewrite the coverage audit's per-section bold tallies and the Totals table from the rows,
after a migration changed Coverage cells. A section's tally is rewritten only where it equals the
section's old printed tally, so prose quoting other numbers is untouched.

Usage: python3 -I docs/provenance/regrade-2026-11/scripts/fix_audit_tallies.py [--write]"""
import importlib.util, os, re, sys
R = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOT = os.path.abspath(os.path.join(R, '..', '..', '..'))
spec = importlib.util.spec_from_file_location('cca', os.path.join(ROOT, 'scripts', 'check_coverage_audit.py'))
cca = importlib.util.module_from_spec(spec); spec.loader.exec_module(cca)
text = cca.AUDIT.read_text(encoding='utf-8')
counts = cca.parse_sections(text)[0]
lines = text.split('\n'); out = []; current = None; n = 0
for line in lines:
    if line.startswith('## '):
        m = cca.SECTION_RE.match(line); current = m.group(2).strip() if m else None
    if current is not None and not line.startswith('|'):
        c = counts[current]
        def sub(m):
            global n
            new = f"**{c['Yes']} Yes, {c['Partial']} Partial, {c['No']} No"
            if m.group(4) is not None: new += f", {c['Beyond']} Beyond"
            if m.group(0) != new: n += 1
            return new
        line = cca.SUMMARY_RE.sub(sub, line)
    out.append(line)
text2 = '\n'.join(out)
# Totals table
rows, _ = cca.parse_totals(text2)
# aligned by position, as the checker aligns them
order = [s for s, v in counts.items() if any(v.values())]
grand = [0, 0, 0, 0]; res = []; t = 0; k = 0; in_totals = False
for line in text2.split('\n'):
    if line.strip() == '## Totals': in_totals = True
    elif in_totals and line.startswith('## '): in_totals = False
    m = cca.TOTALS_ROW_RE.match(line) if in_totals else None
    if m:
        label = m.group(1).strip(); s = order[k]; k += 1
        assert cca.label_matches(label, s), (label, s)
        c = counts[s]; v = [c['Yes'], c['Partial'], c['No'], c['Beyond']]
        grand = [a + b for a, b in zip(grand, v)]
        new = f"| {label} | " + ' | '.join(map(str, v)) + ' |'
        if new != line: t += 1
        line = new
    res.append(line)
text3 = '\n'.join(res)
text3 = re.compile(cca.GRAND_RE.pattern, re.M).sub('| **total** | ' + ' | '.join(f'**{x}**' for x in grand) + ' |', text3)
print(f'{n} section tallies, {t} totals rows rewritten; grand {grand}')
if '--write' in sys.argv: cca.AUDIT.write_text(text3, encoding='utf-8')
