"""Freeze source hashes after the clean build and compiler extraction.

Run only after `lake clean rq001; lake build` and
`lake env lean tools/ExtractLearningGraph.lean` succeed.
"""
from pathlib import Path
import hashlib, json, sys

root = Path(__file__).resolve().parents[1]
out = root / 'formalization/mathematics-learning/verification'
compiled = root / 'docs/formalization/mathematics-learning/compiled.json'
nodes = json.loads(compiled.read_text(encoding='utf-8'))
modules = sorted({n['module'] for n in nodes})
rows = []
for module in modules:
    path = module.replace('.', '/') + '.lean'
    rows.append({'name': module, 'path': path,
                 'sha256': hashlib.sha256((root / path).read_bytes()).hexdigest()})
log = Path(sys.argv[1]).read_text(encoding='utf-8-sig').replace('\r\n', '\n').encode('utf-8')
assert b'Build completed successfully (8937 jobs).' in log
assert len(modules) == 9 and len(nodes) == 225
assert all(set(n['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for n in nodes)
audit = {'schema_version': 1, 'clean_build_command': 'lake clean rq001; lake build',
         'extract_command': 'lake env lean tools/ExtractLearningGraph.lean',
         'compiled_declarations': len(nodes),
         'compiled_sha256': hashlib.sha256(compiled.read_bytes()).hexdigest(),
         'clean_build_log_sha256': hashlib.sha256(log).hexdigest(),
         'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
         'scope': 'Non-exercise material only; see exercise-exclusions.json and obligations.json.',
         'modules': rows}
(out / 'expanded-clean-build.log').write_bytes(log)
(out / 'expanded-audit.json').write_text(json.dumps(audit, indent=2) + '\n', encoding='utf-8', newline='\n')
print('Recorded the successful nine-module build and 225-declaration audit.')
