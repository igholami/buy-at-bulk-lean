#!/usr/bin/env python3
"""Check elaborated definition/proof dependencies, not mere import reachability.

Build first. With no arguments, inspect BuyAtBulk.paper_main.
Additional qualified declaration names select a cluster of partial results.
Missing final project modules cause exit status 1. The import-only library
entry point is excluded; every module below BuyAtBulk/ is checked.
"""
from pathlib import Path
import re
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent.parent
roots = sys.argv[1:] or ['BuyAtBulk.paper_main']
if any(not re.fullmatch(r'BuyAtBulk(?:\.[A-Za-z_][A-Za-z_0-9]*)+', name) for name in roots):
    raise SystemExit('Use qualified BuyAtBulk declaration names.')
expected = {'.'.join(p.relative_to(root).with_suffix('').parts)
            for p in (root / 'BuyAtBulk').rglob('*.lean')}
lean = '''import BuyAtBulk
import Lean.Util.FoldConsts
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending : Array Name := ROOTS
  let mut seen : NameSet := {}
  let mut modules : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throwError "Unknown declaration {name}"
    if let some idx := env.getModuleIdxFor? name then
      modules := modules.insert env.header.moduleNames[idx]!
    for dependency in info.getUsedConstantsAsSet.toList do
      let s := dependency.toString
      if s.startsWith "BuyAtBulk." || s.startsWith "_private.BuyAtBulk." then
        pending := pending.push dependency
  for moduleName in modules.toList do
    logInfo m!"DEPENDENCY_MODULE {moduleName}"
'''.replace('ROOTS', '#[' + ', '.join('``' + name for name in roots) + ']')
with tempfile.TemporaryDirectory(prefix='buy-at-bulk-dependencies-') as directory:
    audit = Path(directory) / 'Dependencies.lean'
    audit.write_text(lean)
    result = subprocess.run(['lake', 'env', 'lean', '-j2', str(audit)], cwd=root,
                            text=True, capture_output=True)
    if result.returncode:
        print(result.stdout + result.stderr, end='')
        raise SystemExit(result.returncode)
used = set(re.findall(r'DEPENDENCY_MODULE\s+(BuyAtBulk(?:\.\w+)+)', result.stdout))
missing = sorted(expected - used)
print('Declaration roots: ' + ', '.join(roots))
print(f'Elaborated type/value closure uses {len(expected & used)}/{len(expected)} project modules.')
for module in sorted(expected & used):
    print('USED    ' + module)
for module in missing:
    print('MISSING ' + module)
print('This checks actual constant references, including statement types; it does not certify source fidelity.')
if missing:
    print('FAIL: final project modules are missing from the selected proof closure.')
    raise SystemExit(1)
print('PASS: all final project modules occur in the selected declaration closure.')
