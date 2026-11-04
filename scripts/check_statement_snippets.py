#!/usr/bin/env python3
"""Check that statement-map code excerpts are verbatim and cover the main paper theorem.

This checks source synchronization, not mathematical equivalence. Lean excerpts
are declarations in their original module context, not standalone programs.
"""
from pathlib import Path
import argparse
import re
import sys

root = Path(__file__).resolve().parent.parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--paper-dir', type=Path,
                    help='Optional directory containing the paper LaTeX sources.')
args = parser.parse_args()
paper = args.paper_dir.resolve() if args.paper_dir is not None else None
document = (root / 'statements.md').read_text()
pattern = re.compile(r'<!-- (lean|paper)-source: ([^\n]+?) -->\s*```(lean|latex)\n(.*?)\n```', re.S)
errors = []
counts = {'lean': 0, 'paper': 0}
paper_labels = []
for match in pattern.finditer(document):
    kind, relative, language, excerpt = match.groups()
    source = (root / relative) if kind == 'lean' else (paper / relative if paper is not None else None)
    counts[kind] += 1
    if language != {'lean': 'lean', 'paper': 'latex'}[kind]:
        errors.append(f'Wrong fence language for {relative}')
    if source is None:
        pass  # External paper verification is explicitly optional.
    elif not source.is_file():
        errors.append(f'Missing source: {source}')
    elif excerpt.strip() not in source.read_text():
        errors.append(f'Non-verbatim excerpt from {relative}: {excerpt.splitlines()[0]}')
    if kind == 'lean' and re.match(r'(?:@\[[^\]]*\]\s*)?(?:private\s+)?theorem\s', excerpt.strip()):
        # A source-exact prefix can still truncate at a named argument `(D := D)`.
        # Check both nesting and the declaration's proof delimiter.
        cleaned = re.sub(r'/\-.*?\-/', '', excerpt, flags=re.S)
        cleaned = re.sub(r'--[^\n]*', '', cleaned)
        stack = []
        pairs = {')': '(', ']': '[', '}': '{', '⟩': '⟨'}
        for char in cleaned:
            if char in '([{⟨':
                stack.append(char)
            elif char in pairs:
                if not stack or stack.pop() != pairs[char]:
                    errors.append(f'Unbalanced theorem signature in {relative}')
                    break
        if stack:
            errors.append(f'Truncated theorem signature in {relative}: {excerpt.splitlines()[0]}')
        if source.is_file() and excerpt.strip() in source.read_text():
            tail = source.read_text().split(excerpt.strip(), 1)[1].lstrip()
            if not tail.startswith(':='):
                errors.append(f'Theorem excerpt does not end at its proof boundary: {relative}')
    if kind == 'paper':
        labels = re.findall(r'\\label\{([^}]+)\}', excerpt)
        if labels:
            paper_labels.append(labels[0])

fences = re.findall(r'^```(?:lean|latex)\s*$', document, re.M)
if len(fences) != sum(counts.values()):
    errors.append('Some Lean/LaTeX fences lack source annotations.')
expected = ['thm:rounding']
if sorted(paper_labels) != sorted(expected):
    errors.append(f'Paper item coverage differs: missing={sorted(set(expected)-set(paper_labels))}, '
                  f'extra={sorted(set(paper_labels)-set(expected))}; '
                  f'{len(paper_labels)} excerpts for {len(expected)} items.')
for error in errors:
    print('FAIL:', error)
if errors:
    sys.exit(1)
print(f'PASS: {counts["lean"]} verbatim Lean excerpts; main approximation theorem covered.')
if paper is not None:
    print(f'PASS: {counts["paper"]} verbatim paper statement(s).')
else:
    print('Paper-source comparison skipped; supply --paper-dir to verify the external LaTeX excerpt.')
print('Source synchronization only; this does not certify paper/Lean equivalence.')
