#!/usr/bin/env python3
"""Check publication consistency and the retained full-verification receipts."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
RECEIPTS = ROOT / 'data/verification/20260929'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = {'status': 'pass', 'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'checks': {}}
    checks = report['checks']
    artifact = json.loads((RECEIPTS / 'artifact.json').read_text())
    assert artifact['status'] == 'pass' and artifact['full_recomputation'] is True
    assert artifact['checks']['reference_values'] == 51
    assert artifact['checks']['certificate_words'] == 47
    assert artifact['checks']['new_sequence_entries'] == 28
    assert artifact['checks']['previously_displayed_entries'] == 39
    for series in artifact['checks']['solver']:
        raw = ROOT / 'data/raw' / f"{series['mode']}_{series['pattern']}.txt"
        expected = dict(tuple(map(int, line.replace('n=', '').replace('count=', '').split()))
                        for line in raw.read_text().splitlines())
        assert {int(n): v for n, v in series['values'].items()} == expected
    checks['full_direct_recomputation'] = True
    inputs = json.loads((RECEIPTS / 'artifact-inputs.json').read_text())
    for name, digest in inputs['sha256'].items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name
    checks['execution_input_hashes'] = len(inputs['sha256'])
    dp = json.loads((RECEIPTS / 'parent-dp.json').read_text())
    assert dp['status'] == 'pass' and dp['comparisons'] == 47304
    checks['independent_parent_dp_comparisons'] = dp['comparisons']
    assert 'ALL CHECKS PASSED' in (RECEIPTS / 'binary.log').read_text()
    formal = (RECEIPTS / 'lean.log').read_text()
    assert 'Build completed successfully' in formal
    required = ['parent_theoremA_iff', 'parent_theoremB', 'regroup_full_children',
                'theoremA_trees', 'theoremB_trees', 'ubword_iff_tree', 'bword_iff_tree']
    for name in required:
        line = next(line for line in formal.splitlines() if f"BfsWords.{name}' depends on axioms:" in line)
        axioms = line.split('axioms: [', 1)[1].rstrip(']').split(', ')
        assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}
    checks['formal_statements_audited'] = required

    tex = (ROOT / 'paper/main.tex').read_text()
    table = tex.split('\\begin{tabular}', 1)[1].split('\\end{tabular}', 1)[0]
    rows = [line for line in table.splitlines() if re.match(r'^\d+&', line)]
    cells = 0
    for line in rows:
        values = [re.sub(r'[^0-9]', '', value) for value in line.split('&')]
        assert len(values) == 8, line
        n = int(values[0])
        for offset, pat in enumerate((231, 312, 321), 1):
            if values[offset]:
                if n == 15 and pat == 231:
                    expected = 877865
                else:
                    raw = (ROOT / 'data/raw' / f'ub_{pat}.txt').read_text()
                    expected = int(re.search(rf'^n={n} count=(\d+)$', raw, re.M).group(1))
                assert int(values[offset]) == expected, (n, pat)
                cells += 1
        if values[4]:
            length = int(values[4])
            for offset, pat in enumerate((231, 312, 321), 5):
                raw = (ROOT / 'data/raw' / f'b_{pat}.txt').read_text()
                expected = int(re.search(rf'^n={length} count=(\d+)$', raw, re.M).group(1))
                assert int(values[offset]) == expected, (length, pat)
                cells += 1
    assert cells == 28
    checks['paper_table_entries'] = cells

    audited_files = 0
    for p in ROOT.rglob('*'):
        if any(part in ('.git', '.lake', '__pycache__', 'dist', 'staging') for part in p.relative_to(ROOT).parts):
            continue
        if not p.is_file() or p.suffix not in ('.md', '.tex', '.lean', '.py', '.cff', '.yml', '.yaml'):
            continue
        text = p.read_text()
        assert chr(0x2014) not in text, p
        if p.suffix == '.tex':
            assert '---' not in text and '\\textemdash' not in text, p
        if p.suffix == '.lean':
            code = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
            code = re.sub(r'--[^\n]*', '', code)
            assert not re.search(r'\b(?:sorry|admit|axiom)\b', code), p
        audited_files += 1
    checks['source_files_checked_for_em_dash'] = audited_files
    pdf = ROOT / 'paper/main.pdf'
    pdf_hash = hashlib.sha256(pdf.read_bytes()).hexdigest()
    visual = json.loads((RECEIPTS / 'pdf-qa.json').read_text())
    assert visual['status'] == 'pass' and visual['pdf_sha256'] == pdf_hash
    assert visual['pages_reviewed'] == list(range(1, visual['page_count'] + 1))
    checks['pdf_sha256'] = pdf_hash
    checks['pdf_pages_visually_reviewed'] = visual['page_count']
    pdf_text = subprocess.check_output(['pdftotext', str(pdf), '-'], text=True)
    assert chr(0x2014) not in pdf_text
    assert '\ufffd' not in pdf_text and '\u25a0' not in pdf_text
    assert 'Conclusion' in pdf_text and 'References' in pdf_text
    assert 'VERSION_PLACEHOLDER' not in tex
    report['paper_sha256'] = hashlib.sha256(tex.encode()).hexdigest()
    encoded = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
