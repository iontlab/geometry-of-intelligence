/* Reuses the RQ-001 prose renderer and tab controls for source-item inspection. */
'use strict';
window.ILabLearningStatement=(()=>{
 const X=window.ILabExplain;
 let graphPromise,graphHash,nativePromise,nativeHash,nativeSerial=0;
 async function renderNative(host,key,expectedHash,isCurrent=()=>host.isConnected){
  if(!/^[a-f0-9]{64}$/.test(expectedHash||''))throw Error('Missing native-source binding');
  if(nativeHash!==expectedHash){nativeHash=expectedHash;nativePromise=null;}
  if(!nativePromise)nativePromise=(async()=>{
   const response=await fetch(new URL('native-source.json',new URL(X.base,location.origin)),{cache:'no-store'});
   if(!response.ok)throw Error('Original source unavailable');
   const bytes=await response.arrayBuffer();
   if(bytes.byteLength>500000||await X.sha(bytes)!==expectedHash)throw Error('Original source changed');
   return JSON.parse(new TextDecoder('utf-8',{fatal:true}).decode(bytes));
  })();
  const source=await nativePromise,fragment=source.items?.[key];
  if(!fragment||source.source_pdf_sha256!=='5d773c2492817fbc366d7fe31fbac096dadadf2c3d24f616684a50b089f144bc')throw Error('Missing original item');
  if(!isCurrent())return;
  const parsed=new DOMParser().parseFromString(fragment.html,'text/html');
  const tags=new Set(['P','EM','STRONG','UL','LI','DIV','H3','BR','A','svg','g','path','text','circle']);
  const attrs=new Set(['class','id','version','xmlns','xmlns:xlink','width','height','viewBox','stroke-miterlimit','transform','stroke','fill','stroke-width','d','alignment-baseline','x','y','font-family','font-size','fill-opacity','stroke-linecap','cx','cy','r','href','title']);
  const prefix='ilab-native-'+(++nativeSerial)+'-';
  for(const element of parsed.body.querySelectorAll('*')){
   if(!tags.has(element.tagName))throw Error('Unsupported original-source markup');
   for(const attribute of [...element.attributes]){
    if(!attrs.has(attribute.name)||/url\s*\(/i.test(attribute.value))throw Error('Unsupported original-source attribute');
    if(attribute.name==='id')element.id=prefix+attribute.value;
    if(attribute.name==='href'){
     const u=new URL(attribute.value,location.origin);
     if(!['http:','https:'].includes(u.protocol))throw Error('Unsupported source link');
    }
   }
  }
  const body=X.element('div');body.className='ilab-native-source';body.hidden=true;
  body.append(...parsed.body.childNodes);host.append(body);
  if(!document.querySelector('link[href="https://iontlab.org/lib/plugins/tikzjax/lib/fonts.css"]')){
   const fonts=document.createElement('link');fonts.rel='stylesheet';fonts.href='https://iontlab.org/lib/plugins/tikzjax/lib/fonts.css';document.head.append(fonts);
  }
  if(typeof loadMathRenderer==='function')await loadMathRenderer();
  else if(window.MathJax?.startup?.promise)await window.MathJax.startup.promise;
  if(!window.MathJax?.typesetPromise)throw Error('Mathematics renderer unavailable');
  if(!isCurrent()){body.remove();return;}
  await window.MathJax.typesetPromise([body]);
  if(body.querySelector('mjx-merror,[data-mjx-error],[data-mml-node="merror"]'))throw Error('Original formula rendering failed');
  if(!isCurrent()){body.remove();return;}
  body.hidden=false;
  host.append(X.element('p','Original manuscript — Lyne Moser and Tashi Walde. Original proofs, partial proofs and exercise markers are retained.'));
 }
 async function graph(state){
  if(graphHash!==state.reg.graph.data_sha256){graphHash=state.reg.graph.data_sha256;graphPromise=null;}
  if(!graphPromise)graphPromise=(async()=>{
   const response=await fetch(new URL('../data.json',new URL(X.base,location.origin)),{cache:'no-store'});
   if(!response.ok)throw Error('Compiled graph unavailable');
   const bytes=await response.arrayBuffer();
   if(await X.sha(bytes)!==state.reg.graph.data_sha256)throw Error('Compiled graph changed');
   return JSON.parse(new TextDecoder('utf-8',{fatal:true}).decode(bytes));
  })();return graphPromise;
 }
 function link(host,label,url){const a=X.element('a',label);a.href=url;host.append(a);}
 async function render(host,r,view,state,isCurrent=()=>host.isConnected){
  if(!isCurrent())return;
  host.replaceChildren();
  if(['Plain','Story'].includes(view)){X.render(host,r,view);return;}
  host.append(X.element('h4',r.source.heading_text));
  if(view==='Mathematics'){
   await renderNative(host,r.source.item_key,state.reg.native_source_sha256,isCurrent);
  }else{
   host.append(X.element('p',r.formal_mapping.status));
   for(const scope of new Set((r.obligations||[]).map(o=>o.scope).filter(Boolean)))host.append(X.element('p',scope));
   const ids=r.formal_mapping.declarations||[],d=await graph(state);
   if(!isCurrent())return;
   if(!ids.length)host.append(X.element('p','No checked Lean declaration is mapped to this source item in this release. This is not a verification claim.'));
   for(const id of ids){
    const n=d.nodes.find(n=>n.id===id);if(!n||!n.authored)throw Error('Invalid formal mapping');
    host.append(X.element('h4',id));
    if(view==='Lean')host.append(X.element('pre',n.signature),X.element('p',n.module));
    else host.append(X.element('p',n.verification),X.element('p','Compiler-derived axiom dependencies: '+(n.axioms.join(', ')||'None.')),X.element('p','Direct project dependencies: '+(n.dependencies.join(', ')||'None.')));
    link(host,'Checked source · pinned commit ↗',X.sourceURL(n.sourceUrl));
    const u=new URL('../',new URL(X.base,location.origin));u.searchParams.set('declaration',id);u.searchParams.set('layer',view.toLowerCase());
    link(host,'Open this declaration in the graph ↗',u.href);
   }
   if(view==='Verification'){
    link(host,'Source-to-Lean fidelity audit ↗',new URL('../source-audit.json',new URL(X.base,location.origin)).href);
    host.append(X.element('p',`Lean ${d.lean} · Mathlib ${d.mathlib} · revision ${d.mathlibRevision}`),X.element('p','Primary PDF SHA-256: '+r.source.primary_sha256),X.element('p','Bound chapter revision: '+r.source.revision),X.element('p','Bound chapter SHA-256: '+r.source.whole_page_sha256));
    for(const obligation of r.obligations||[])host.append(X.element('p',obligation.id+' · '+obligation.status+' · '+obligation.statement));
   }
  }
  link(host,'Exact chapter statement · pinned edition ↗',X.sourceURL(r.source.source_link));
 }
 return {render,graph,renderNative};
})();
