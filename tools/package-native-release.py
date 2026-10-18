"""Package only existing learning asset paths for the established WebFTP workflow."""
from pathlib import Path
import datetime, hashlib, json, re, zipfile
R=Path(__file__).resolve().parents[1];G=R/'docs/formalization/mathematics-learning'
W=R.parent/'mathematics-learning-20261018/native-publication'
release=json.loads((G/'explanations/release.json').read_text(encoding='utf8'))['release']
audit=json.loads((R/'docs/mathematics-learning/original/native/source-audit.json').read_text(encoding='utf8'))
graph=json.loads((G/'data.json').read_text(encoding='utf8'))
index=(G/'index.html').read_text(encoding='utf8')
index=re.sub(r'learning-(?:non-exercise|native)-20261018-[A-Za-z0-9-]+',release,index)
index=re.sub(r'Checked source modules <b>\d+</b>',f"Checked source modules <b>{len(graph['modules'])}</b>",index)
index=index.replace('the nine checked learning modules','the checked learning modules')
index=index.replace('/tree/main/formalization/mathematics-learning','/tree/codex/source-faithful-native-manuscript/formalization/mathematics-learning')
index=index.replace('These declarations check ordinary Mathlib category theory.', 'The checked implementation includes source-faithful set-coded categories and explicitly distinguished independent Mathlib support.')
index=index.replace('Checked scope includes ordinary category definitions and examples, non-exercise Yoneda consequences, adjunction examples, the equivalence criterion, set-universe assumptions, and paths up to endpoint-fixed homotopy. Source items retain their individual limitations.', 'Complete original-item verification is recorded in the source audit. Items 1.8, 1.10, 1.13, 1.16, 2.7 and 3.2 remain incomplete; related compiled examples do not close those obligations.')
index=index.replace('Checked ordinary-category material · assigned exercise solutions withheld','23 exact numbered items verified · 6 eligible items pending · assigned exercise solutions withheld')
index=index.replace('Mathematical explanations and proof sketches are independently authored educational metadata, distinct from compiler output. No mathematical novelty is claimed.',
    'Mathematics panels reproduce the original manuscript. Story and Plain Language remain independent supplementary explanations. Source fidelity is assessed separately from compilation; the six pending original items are listed in the source audit.')
index=re.sub(r'<p class="status">.*?</p>',f'<p class="status">{audit["fully_formalized"]} exact numbered items verified · {audit["pending_eligible_items"]} eligible numbered items pending · assigned exercise solutions withheld</p>',index)
index=index.replace('Complete original-item verification is recorded in the source audit. Items 1.8, 1.10, 1.13, 1.16, 2.7 and 3.2 remain incomplete; related compiled examples do not close those obligations.',
  'Every mathematically specified non-exercise numbered item is verified in the source set-universe representation. The item-level source audit records the exact correspondences. Later higher/synthetic axioms remain deferred.')
index=index.replace('Source fidelity is assessed separately from compilation; the six pending original items are listed in the source audit.',
  'Source fidelity is assessed separately from compilation. The source audit distinguishes verified non-exercise items, withheld assignments and prospective higher foundations.')
(G/'index.html').write_text(index,encoding='utf8',newline='\n')
(G/'source-audit.json').write_bytes((R/'docs/mathematics-learning/original/native/source-audit.json').read_bytes())
files=[G/n for n in ['index.html','style.css','app.js','blueprint-view.js','mathematics-view.js','data.json','compiled.json','mathematics.json','source-audit.json']]
files += [G/'explanations'/n for n in ['renderer.js','graph-adapter.js','statement-adapter.js','wiki-adapter.js','explanations.css','registry.v0.1.json','release.json','binding.json','native-source.json']]
manifest=[]
with zipfile.ZipFile(W/(release+'.zip'),'w',zipfile.ZIP_DEFLATED) as z:
    for p in files:
        name='public_html/formalization/mathematics-learning/'+p.relative_to(G).as_posix()
        info=zipfile.ZipInfo(name,datetime.datetime.now().timetuple()[:6]);info.create_system=3
        info.external_attr=0o100644<<16;info.compress_type=zipfile.ZIP_DEFLATED
        b=p.read_bytes();z.writestr(info,b)
        manifest.append({'path':name,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)})
(W/(release+'-files.json')).write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf8')
print(f'Packaged {len(files)} learning-only files: {release}.zip')
