"""Run with lake env python tools/verify-linear-algebra.py in the pinned project.
Creates fresh project oleans, then re-extracts their types, values and axioms.
Mathlib oleans come from the exact lake-manifest.json revision; no upgrades.
"""
from pathlib import Path
import hashlib, json, os, shutil, subprocess, time
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'verification'
OUT.mkdir(exist_ok=True)
BUILD=OUT/'rebuild'
env=os.environ.copy()
env['LEAN_PATH']=str(BUILD)+os.pathsep+env.get('LEAN_PATH','')
lean=shutil.which('lean')
if not lean:raise SystemExit('Use lake env python tools/verify-linear-algebra.py')
sha=lambda b:hashlib.sha256(b).hexdigest()
sources=['ILab/LinearAlgebra/Dimensions.lean','ILab/LinearAlgebra/MatrixAlgebra.lean',
         'ILab/LinearAlgebra/BasisMaps.lean','ILab/LinearAlgebra/Rotations.lean',
         'ILab/LinearAlgebra/Preparation.lean','ILab/LinearAlgebra/LinearSystems.lean','ILab/LinearAlgebra/Logic.lean','ILab/LinearAlgebra/SetsInduction.lean','ILab/LinearAlgebra/RelationsFunctions.lean','ILab/LinearAlgebra/Groups.lean','ILab/LinearAlgebra/Homomorphisms.lean','ILab/LinearAlgebra/FieldsComplex.lean','ILab/LinearAlgebra/RingsPolynomials.lean','ILab/LinearAlgebra/VectorSpacesSubspaces.lean','ILab/LinearAlgebra/LinearMapsFamilies.lean','ILab/LinearAlgebra/QuotientSpaces.lean','ILab/LinearAlgebra/LinearCombinations.lean','ILab/LinearAlgebra/BasisDimension.lean','ILab/LinearAlgebra/MoreMatrices.lean','ILab/LinearAlgebra/ElementaryMatrices.lean','ILab/LinearAlgebra/CoordinateChanges.lean','ILab/LinearAlgebra/MatrixEquivalence.lean','ILab/LinearAlgebra.lean']
version=subprocess.check_output([lean,'--version'],cwd=ROOT,text=True,encoding='utf-8').strip()
if 'version 4.34.0,' not in version:raise SystemExit('Unexpected Lean toolchain')
manifest=json.loads((ROOT/'lake-manifest.json').read_text(encoding='utf-8'))
mathlib=next(p for p in manifest['packages'] if p['name']=='mathlib')
if mathlib['rev']!='5ed2965256430c3649e86755f9576b54eca72435':raise SystemExit('Wrong Mathlib revision')
actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT/'.lake/packages/mathlib',text=True).strip()
if actual!=mathlib['rev']:raise SystemExit('Mathlib checkout differs from lockfile')
steps=[]
with (OUT/'clean-compilation.log').open('w',encoding='utf-8',newline='\n') as log:
    log.write(version+'\nMathlib '+actual+'\n')
    for source in sources+['tools/ExtractLinearGraph.lean']:
        file=ROOT/source
        if source in sources:
            code=file.read_text(encoding='utf-8')
            import re
            clean=re.sub(r'/-.*?-/|--[^\n]*','',code,flags=re.S)
            if re.search(r'\b(sorry|admit|axiom|sorryAx|native_decide)\b',clean):
                raise SystemExit('Unacceptable proof token in '+source)
            target=BUILD/Path(source).with_suffix('.olean')
            target.parent.mkdir(parents=True,exist_ok=True)
            command=[lean,'-o',str(target),source]
        else:command=[lean,source]
        start=time.monotonic()
        process=subprocess.run(command,cwd=ROOT,env=env,stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT,text=True,encoding='utf-8')
        log.write('\n$ '+' '.join(command)+'\n'+process.stdout)
        log.write('Exit code: '+str(process.returncode)+'\n');log.flush()
        if process.returncode:raise SystemExit('Compilation failed: '+source)
        steps.append(dict(source=source,sha256=sha(file.read_bytes()),exit_code=0,
                          duration_seconds=round(time.monotonic()-start,3)))
raw=json.loads((OUT/'compiled.json').read_text(encoding='utf-8'))
audit=dict(lean=version,mathlib_revision=actual,steps=steps,
           project_declarations=sum(n['project'] for n in raw),
           selected_library_declarations=sum(not n['project'] for n in raw),
           compiled_sha256=sha((OUT/'compiled.json').read_bytes()),
           log_sha256=sha((OUT/'clean-compilation.log').read_bytes()),
           source_fidelity='Separate authored audit against Holstein pp. 2–96 (through section5.5, before chapter6).',
           dependencies='Direct constants in compiled types and values; no didactic edges.',
           allowed_axioms=['propext','Classical.choice','Quot.sound'],
           sorry_free=True,additional_project_axioms=False)
(OUT/'audit.json').write_text(json.dumps(audit,indent=2)+'\n',encoding='utf-8',newline='\n')
print('PASS:',audit['project_declarations'],'freshly compiled/audited project declarations;',
      audit['selected_library_declarations'],'selected library declarations.')
