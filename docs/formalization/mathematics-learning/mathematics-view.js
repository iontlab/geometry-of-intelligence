'use strict';
// Authored educational presentations are separate from compiled graph/audit metadata.
const authoredMathematics = fetch('mathematics.json',{cache:'no-store'}).then(r => {
  if (!r.ok) throw new Error(`HTTP ${r.status}`);
  return r.arrayBuffer().then(buffer=>{window.ILabExplainGraph?.loaded('mathematics',buffer);return JSON.parse(new TextDecoder('utf-8',{fatal:true}).decode(buffer))});
}).catch(() => null);
let mathRenderer;
function loadMathRenderer() {
  if (!mathRenderer) mathRenderer = new Promise((resolve, reject) => {
    // Reuse the same MathJax bundle already used by the live iLab Research Note.
    window.MathJax = {tex: {inlineMath: [['\\(', '\\)']], displayMath: [['\\[', '\\]'], ['$$','$$']]},
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
async function showDeclaration(n,requestedExplanation=null) {
  const request = ++detailRequest, panel = $('detail');
  panel.dataset.inspector='declaration';
  if (window.MathJax?.typesetClear) window.MathJax.typesetClear([panel]);
  panel.replaceChildren(html('div', 'DECLARATION INSPECTOR'), html('h2', n.id));
  panel.firstChild.className = 'detail-label';
  panel.append(html('p', `${n.kind} · ${n.authored ? 'authored declaration' : 'compiler-generated declaration'}`));
  const metadata = await authoredMathematics;
  if (request !== detailRequest) return;
  const mapping = metadata?.declarations[n.id], result = mapping && metadata.results[mapping.result];
  let explanation=null;
  // Optional services never delay the original technical views.
  const names = result ? ['Mathematics','Lean','Verification'] : ['Lean','Verification'];
  const tabs = html('div'); tabs.className = 'detail-tabs'; tabs.setAttribute('role', 'tablist');
  tabs.setAttribute('aria-label', 'Declaration views'); panel.append(tabs);
  function makePane(name) {
    const pane = html('section'); pane.id = 'declaration-'+name.toLowerCase();
    pane.setAttribute('role', 'tabpanel'); pane.setAttribute('aria-labelledby', pane.id+'-tab');
    pane.tabIndex = 0; if(['Plain','Story'].includes(name))pane.classList.add('ilab-explain'); pane.hidden=true; panel.append(pane); return pane;
  }
  const panes=names.map(makePane);
  function makeButton(name,pane) {
    const b = html('button', name); b.type = 'button'; b.id = pane.id+'-tab';
    if(['Plain','Story'].includes(name))b.classList.add('ilab-explain'); b.setAttribute('role', 'tab'); b.setAttribute('aria-controls', pane.id);
    b.onclick = () => { activate(names.indexOf(name)); const u=new URL(location.href);u.searchParams.delete('statement');u.searchParams.set('declaration',n.id);u.searchParams.set('layer',name.toLowerCase());history.replaceState(null,'',u); };
    b.onkeydown = e => {
      let next; const live=buttons.filter(b=>b.isConnected),position=live.indexOf(b),at=n=>buttons.indexOf(live[n]);
      if (e.key === 'ArrowRight') next = at((position+1)%live.length);
      if (e.key === 'ArrowLeft') next = at((position+live.length-1)%live.length);
      if (e.key === 'Home') next = at(0);
      if (e.key === 'End') next = at(live.length-1);
      if (next !== undefined) { e.preventDefault(); activate(next); buttons[next].focus(); }
    };
    tabs.append(b); return b;
  }
  const buttons=names.map((name,i)=>makeButton(name,panes[i]));
  function activate(index) {
    if(['Plain','Story'].includes(names[index])&&!window.ILabExplainGraph?.isCurrent(explanation)){index=0;}
    if(['Plain','Story'].includes(names[index]))window.ILabExplainGraph.render(panes[index],explanation,names[index]);
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
  audit.append(n.dependencies.length ? ul : html('p','None.'), html('h3','Axiom dependencies'), html('p', n.axioms.length?n.axioms.join(', '):'None.'), html('p','Foundational Lean axioms are not project-added assumptions.'), html('h3','Lesson mapping — authored metadata'), html('p',n.paperMapping.text), html('p',n.paperMapping.provenance), sourceLink(n));
  activate(names.includes(requestedExplanation)?names.indexOf(requestedExplanation):0);
  // Attach only to this still-current selection, preserving its active technical tab and focus.
  window.ILabExplainGraph?.selection(n,data,metadata,requestedExplanation).then(context=>{
    if(request!==detailRequest||!panel.isConnected||!window.ILabExplainGraph.isCurrent(context))return;
    explanation=context;
    if(context.kind==='supporting') {
      const notice=html('div');notice.className='ilab-explain ilab-explain-context';
      notice.append(html('p','Plain and Story explain the main result: '+context.r.source.heading_text+'.'));
      const action=html('button','Explain main result →');action.type='button';action.onclick=()=>window.ILabExplainGraph.navigate(context);notice.append(action);tabs.after(notice);return;
    }
    for(const [offset,name] of ['Plain','Story'].entries()){
      const i=1+offset;names.splice(i,0,name);const pane=makePane(name);panes.splice(i,0,pane);
      const button=makeButton(name,pane);buttons.splice(i,0,button);tabs.insertBefore(button,buttons[i+1]);
      panel.insertBefore(pane,panes[i+1]);button.tabIndex=-1;button.setAttribute('aria-selected','false');
    }
    tabs.classList.add('ilab-explain','ilab-explain-five');panel.classList.add('ilab-explain-inspector');
    if(context.s.preview){const notice=html('p',window.ILabExplain.notice);notice.className='ilab-explain ilab-explain-notice';tabs.before(notice);}
    context.cleanup=()=>{if(buttons.some((b,i)=>['Plain','Story'].includes(names[i])&&b.getAttribute('aria-selected')==='true'))activate(0);};
    if(['Plain','Story'].includes(requestedExplanation))activate(names.indexOf(requestedExplanation));
  }).catch(()=>{});
  if (!result) return;
  if(result.native_key){
    const math=panes[0];
    math.append(html('p',result.limitation||''));
    try{await window.ILabLearningStatement.renderNative(math,result.native_key,metadata.native_source_sha256,()=>request===detailRequest&&math.isConnected);}
    catch{if(request===detailRequest)math.append(html('p','The bound original source could not render. Read the linked chapter for the original statement.'));}
    return;
  }
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
  const paper=html('a',`Published lesson · ${result.label} ↗`);paper.href=(result.source||metadata.source)+(result.anchor?'#'+result.anchor:'');paper.target='_blank';paper.rel='noopener';body.append(paper);
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
  }).catch(()=>{if(request===detailRequest){loading.textContent='Mathematics could not render. Read the published lesson; Lean and Verification remain available.';const link=paper.cloneNode(true);math.append(link);}});
}
