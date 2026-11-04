#!/usr/bin/env python3
"""Build first, then check imported project theorem axioms and import coverage.
This checks kernel dependencies; source fidelity and runtime are separate.
"""
from pathlib import Path
import re
import subprocess
import tempfile

root = Path(__file__).resolve().parent.parent
sources = [root / 'BuyAtBulk.lean', *sorted((root / 'BuyAtBulk').rglob('*.lean'))]
modules = {'.'.join(p.relative_to(root).with_suffix('').parts): p for p in sources}
for p in sources:
    if re.search(r'\b(sorry|admit|sorryAx)\b|^\s*(axiom|unsafe)\b', p.read_text(), re.M):
        raise SystemExit(f'Unfinished or unchecked declaration: {p.relative_to(root)}')
seen = set()
def visit(module):
    if module in seen or module not in modules:
        return
    seen.add(module)
    for dependency in re.findall(r'^import\s+(\S+)', modules[module].read_text(), re.M):
        visit(dependency)
visit('BuyAtBulk')
if set(modules) != seen:
    raise SystemExit(f'Modules outside library imports: {sorted(set(modules) - seen)}')
with tempfile.TemporaryDirectory(prefix='buy-at-bulk-audit-') as directory:
    audit = Path(directory) / 'Audit.lean'
    audit.write_text('''import BuyAtBulk
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let s := name.toString
    if s.startsWith "BuyAtBulk." || s.startsWith "_private.BuyAtBulk." then
      if info.isTheorem then
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unexpected axiom {ax} in {name}"
        count := count + 1
  logInfo m!"Checked {count} project theorems: standard axioms only."
#print axioms BuyAtBulk.integral_relaxation
#print axioms BuyAtBulk.zero_buying_approximation
#print axioms BuyAtBulk.node_lower_bound
#print axioms BuyAtBulk.parameterized_rounding
#print axioms BuyAtBulk.optimized_rounding
#print axioms BuyAtBulk.approximation
#print axioms BuyAtBulk.exact_polynomial_lp
#print axioms BuyAtBulk.parameterized_polynomial
#print axioms BuyAtBulk.integral_graph_approximation
#print axioms BuyAtBulk.polynomial_graph_approximation
#print axioms BuyAtBulk.supplied_polynomial_rounding
#print axioms BuyAtBulk.selected_zero_rounding
#print axioms BuyAtBulk.computed_network_rounding
#print axioms BuyAtBulk.supplied_sparse_decomposition
#print axioms BuyAtBulk.paper_main
''')
    subprocess.run(['lake', 'env', 'lean', '-j2', str(audit)], cwd=root, check=True)
print(f'{len(sources)} final modules import-reachable from BuyAtBulk.')
print('Import coverage is not substantive main-theorem dependency coverage.')
print('Axiom checks certify kernel dependencies; source fidelity and the operation model require the separate audit.')
