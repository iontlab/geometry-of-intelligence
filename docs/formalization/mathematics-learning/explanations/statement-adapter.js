/* Reuses the RQ-001 prose renderer and tab controls for source-item inspection. */
'use strict';
window.ILabLearningStatement=(()=>{
 const X=window.ILabExplain;
 let graphPromise,graphHash;
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
   for(const text of r.mathematics.statement)host.append(X.element('p',text));
   host.append(X.element('h4','Proof / construction status'));
   for(const text of r.mathematics.proof)host.append(X.element('p',text));
   host.append(X.element('p','Independent iLab exposition; the Moser–Walde source numbering and mathematical scope are authoritative.'));
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
    host.append(X.element('p',`Lean ${d.lean} · Mathlib ${d.mathlib} · revision ${d.mathlibRevision}`),X.element('p','Primary PDF SHA-256: '+r.source.primary_sha256),X.element('p','Bound chapter revision: '+r.source.revision),X.element('p','Bound chapter SHA-256: '+r.source.whole_page_sha256));
    for(const obligation of r.obligations||[])host.append(X.element('p',obligation.id+' · '+obligation.status+' · '+obligation.statement));
   }
  }
  link(host,'Exact chapter statement · pinned edition ↗',X.sourceURL(r.source.source_link));
 }
 return {render,graph};
})();
