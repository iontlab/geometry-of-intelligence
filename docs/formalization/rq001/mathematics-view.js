'use strict';
// Authored paper presentations are separate from compiled graph/audit metadata.
const authoredMathematics = fetch('mathematics.json').then(r => {
  if (!r.ok) throw new Error(`HTTP ${r.status}`);
  return r.json();
}).catch(() => null);
let mathRenderer;
function loadMathRenderer() {
  if (!mathRenderer) mathRenderer = new Promise((resolve, reject) => {
    // Reuse the same MathJax bundle already used by the live iLab Research Note.
    window.MathJax = {tex: {inlineMath: [['\\(', '\\)']], displayMath: [['\\[', '\\]']]},
      svg: {fontCache: 'local'}, startup: {typeset: false}};
    const script = document.createElement('script');
    script.src = 'https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-svg-full.js';
    script.onload = () => window.MathJax.startup.promise.then(resolve, reject);
    script.onerror = () => reject(new Error('Mathematics renderer unavailable'));
    document.head.append(script);
  });
  return mathRenderer;
}
let detailRequest = 0, mathQueue = Promise.resolve();
function sourceLink(n) {
  const a = html('a', `View Lean source${n.line ? ' · line '+n.line : ''} ↗`);
  a.href = n.sourceUrl; a.target = '_blank'; a.rel = 'noopener'; return a;
}
function addParagraphs(parent, paragraphs) {
  for (const text of paragraphs || []) {
    const p = html('p', text);
    if (text.startsWith('\\[')) p.className = 'math-equation';
    parent.append(p);
  }
}
async function showDeclaration(n) {
  const request = ++detailRequest, panel = $('detail');
  if (window.MathJax?.typesetClear) window.MathJax.typesetClear([panel]);
  panel.replaceChildren(html('div', 'DECLARATION INSPECTOR'), html('h2', n.id));
  panel.firstChild.className = 'detail-label';
  panel.append(html('p', `${n.kind} · ${n.authored ? 'authored declaration' : 'compiler-generated declaration'}`));
  const metadata = await authoredMathematics;
  if (request !== detailRequest) return;
  const mapping = metadata?.declarations[n.id], result = mapping && metadata.results[mapping.result];
  const names = result ? ['Mathematics', 'Lean', 'Verification'] : ['Lean', 'Verification'];
  const tabs = html('div'); tabs.className = 'detail-tabs'; tabs.setAttribute('role', 'tablist');
  tabs.setAttribute('aria-label', 'Declaration views'); panel.append(tabs);
  const panes = names.map(name => {
    const pane = html('section'); pane.id = 'declaration-'+name.toLowerCase();
    pane.setAttribute('role', 'tabpanel'); pane.setAttribute('aria-labelledby', pane.id+'-tab');
    pane.tabIndex = 0; panel.append(pane); return pane;
  });
  const buttons = names.map((name, i) => {
    const b = html('button', name); b.type = 'button'; b.id = panes[i].id+'-tab';
    b.setAttribute('role', 'tab'); b.setAttribute('aria-controls', panes[i].id);
    b.onclick = () => activate(i);
    b.onkeydown = e => {
      let next;
      if (e.key === 'ArrowRight') next = (i+1)%names.length;
      if (e.key === 'ArrowLeft') next = (i+names.length-1)%names.length;
      if (e.key === 'Home') next = 0;
      if (e.key === 'End') next = names.length-1;
      if (next !== undefined) { e.preventDefault(); activate(next); buttons[next].focus(); }
    };
    tabs.append(b); return b;
  });
  function activate(index) {
    buttons.forEach((b, i) => { b.setAttribute('aria-selected', String(i===index)); b.tabIndex=i===index?0:-1; panes[i].hidden=i!==index; });
  }
  const lean = panes[names.indexOf('Lean')];
  lean.append(html('h3', 'Lean signature / statement'), html('pre', n.signature), html('h3', 'Source module'), html('p', n.module), sourceLink(n));
  if (!result) lean.append(html('p', metadata ? 'Mathematics view not separately authored for this internal declaration.' : 'Authored mathematics metadata could not load. Lean and verification information remain available.'));
  const audit = panes[names.indexOf('Verification')];
  const status = html('p'); status.append(html('strong', 'Status: '), document.createTextNode(mapping?.role==='principal' ? 'Lean-verified' : 'Compiled / verified declaration'));
  audit.append(status, html('p', n.verification), html('p', `Lean ${data.lean} · Mathlib ${data.mathlib}`), html('p', `Mathlib revision: ${data.mathlibRevision}`), html('h3', 'Direct project-local dependencies'));
  const ul = html('ul');
  for (const dep of n.dependencies) {
    const li=html('li'), b=html('button',short(dep)); b.type='button';
    b.onclick=()=>{if(!byId.get(dep).authored)$('generated').checked=true;$('search').value='';$('module').value=byId.get(dep).module;select(dep)};
    li.append(b); ul.append(li);
  }
  audit.append(n.dependencies.length ? ul : html('p','None.'), html('h3','Axiom dependencies'), html('p', n.axioms.length?n.axioms.join(', '):'None.'), html('p','Foundational Lean axioms are not project-added assumptions.'), html('h3','Paper mapping — authored metadata'), html('p',n.paperMapping.text), html('p',n.paperMapping.provenance), sourceLink(n));
  activate(0);
  if (!result) return;
  const math = panes[0], loading = html('p','Rendering mathematics…'); loading.setAttribute('role','status');
  const body = html('div'); body.className='mathematics-body'; body.hidden=true;
  math.append(loading,body);
  body.append(html('p',mapping.role==='supporting'?`Supporting declaration for ${result.label}`:result.label),html('h3',result.title));
  body.append(html('h3','Mathematical statement'));
  addParagraphs(body,mapping.statement || result.statement);
  if (mapping.role==='principal') {
    if (result.universalProperty) {const universal=html('div');universal.className='universal-property';universal.append(html('h3','Universal property'));addParagraphs(universal,[result.universalProperty]);body.append(universal);addParagraphs(body,[result.notation]);}
    body.append(html('h3','Proof')); addParagraphs(body,result.proof);
    if(result.interpretation)addParagraphs(body,[result.interpretation]);
  }
  if(result.limitation)addParagraphs(body,[result.limitation]);
  const provenance=html('p',metadata.provenance);provenance.className='math-provenance';body.append(provenance);
  const paper=html('a',`Published Research Note · ${result.label} ↗`);paper.href=metadata.source+'#'+result.anchor;paper.target='_blank';paper.rel='noopener';body.append(paper);
  if (mapping.role==='supporting') {
    const principal=Object.entries(metadata.declarations).find(([,m])=>m.result===mapping.result&&m.role==='principal')?.[0];
    if(principal){const p=html('p'),b=html('button','Read full statement and proof');b.type='button';b.onclick=()=>select(principal);p.append(b);body.append(p);}
  }
  // Serialize MathJax work; never expose raw delimiters while loading or on error.
  mathQueue=mathQueue.catch(()=>{}).then(async()=>{
    await loadMathRenderer();
    if(request!==detailRequest)return;
    await window.MathJax.typesetPromise([body]);
    if(request!==detailRequest){window.MathJax.typesetClear([body]);return;}
    if(body.querySelector('mjx-merror,[data-mjx-error]'))throw new Error('Formula rendering failed');
    loading.remove();body.hidden=false;
  }).catch(()=>{if(request===detailRequest){loading.textContent='Mathematics could not render. Read the published Research Note; Lean and Verification remain available.';const link=paper.cloneNode(true);math.append(link);}});
}
