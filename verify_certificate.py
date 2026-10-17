#!/usr/bin/env python3
"""Validate the conditional source certificate against a fresh Lean audit log."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def code_only(text):
    """Remove nested Lean comments and strings before checking proof markers."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif text.startswith('/-', i):
            out.append(' ')
            depth = 1
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            out.append(' ')
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            out.append(text[i])
            i += 1
    require(depth == 0, 'Unclosed Lean comment')
    return ''.join(out)


def verify(audit_path):
    source = ROOT / 'source/SRW_max_local_time.tex'
    expected_hash = '522bdfaea66d101c17e6228f23ef993413928d517afccd66b784c66f89fefb74'
    require((ROOT / 'source/SHA256SUMS').read_text().split()[0] == expected_hash,
            'Certificate source hash manifest changed')
    require(hashlib.sha256(source.read_bytes()).hexdigest() == expected_hash,
            'Source manuscript checksum mismatch')
    source_text = source.read_text()
    label_matches = list(re.finditer(r'\\label\{([^}]+)\}', source_text))
    labels = [match.group(1) for match in label_matches]
    require(len(labels) == len(set(labels)), 'Duplicate source labels')
    label_lines = {match.group(1): source_text.count('\n', 0, match.start()) + 1
                   for match in label_matches}
    records = json.loads((ROOT / 'obligations.json').read_text())
    registered = [r['source_label'] for r in records]
    require(len(registered) == len(set(registered)) == 189, 'Duplicate/missing obligations')
    require(set(registered) == {x for x in labels if not x.startswith('sec:')},
            'Source obligation coverage mismatch')
    require(all(record['line'] == label_lines[record['source_label']] for record in records),
            'Source obligation line mismatch')
    require(Counter(r['status'] for r in records) ==
            Counter(certified=98, conditionally_certified=89, external_assumption=2),
            'Final obligation status mismatch')
    audit = Path(audit_path).read_text()
    require('error:' not in audit, 'Lean audit contains an error')
    rows = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", audit)
    requested = re.findall(r'^#print axioms (\S+)',
                          (ROOT / 'formalization/SRWTightness/Audit.lean').read_text(), re.M)
    require(Counter(name for name, _ in rows) == Counter(requested),
            'Audit does not cover exactly the current requested declarations')
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    require(all(set(re.findall(r'[\w.]+', deps)) <= allowed for _, deps in rows),
            'Nonstandard axiom in audit')
    audited = {name for name, _ in rows}
    for record in records:
        if record['status'] == 'external_assumption':
            continue
        names = record.get('lean_declaration') or []
        names = [names] if isinstance(names, str) else names
        require(names and set(names) <= audited,
                f"Missing directly audited binding: {record['source_label']}")
    seen, pending = set(), ['SRWTightness', 'SRWTightness.Audit']
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        path = ROOT / 'formalization' / (module.replace('.', '/') + '.lean')
        require(path.exists(), f'Missing local imported module: {module}')
        seen.add(module)
        text = code_only(path.read_text())
        require(not re.search(r'\b(sorry|admit|axiom|native_decide)\b', text),
                f'Forbidden proof marker: {module}')
        for imports in re.findall(r'^\s*import[ \t]+([^\n]+)', text, re.M):
            pending.extend(name for name in imports.split() if name.startswith('SRWTightness'))
    print(f'PASS: 189 source obligations; 98 internal, 89 conditional, 2 external, 0 open.')
    print(f'PASS: {len(rows)} audit entries, {len(seen)} rooted modules; standard axioms only.')


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('Usage: python3 verify_certificate.py AUDIT_LOG')
    verify(sys.argv[1])
