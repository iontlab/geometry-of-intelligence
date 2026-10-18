'use strict';
window.ILabExplainGraph=(()=>{
 const X=window.ILabExplain;if(!X)return null;const bytes={};let serial=0,current=null,pending=null;
 function loaded(name,buffer){bytes[name]=X.sha(buffer);}
 function clear(){serial++;const old=current;current=null;pending=null;old?.cleanup?.();
  if(document.getElementById('detail')?.dataset.inspector==='source')return;
  document.querySelectorAll('#detail .ilab-explain[role=tablist]').forEach(e=>e.classList.remove('ilab-explain','ilab-explain-five'));
  document.querySelectorAll('#detail .ilab-explain').forEach(e=>e.remove());
  document.getElementById('detail')?.classList.remove('ilab-explain-inspector');
 }
 async function selection(n,data,metadata,requestedView=null){clear();const ticket=serial;pending={node:n,view:requestedView};
  try{
   const mapping=metadata?.declarations?.[n.id];if(!mapping||!['principal','supporting'].includes(mapping.role))return null;
   const principals=Object.entries(metadata.declarations).filter(([,m])=>m.result===mapping.result&&m.role==='principal');if(principals.length!==1)return null;
   const principal=data.nodes.find(x=>x.id===principals[0][0]);if(!principal)return null;
   const s=await X.load(),matches=s.reg.records.filter(r=>r.formal_mapping.declaration===principal.id);if(matches.length!==1)return null;const r=matches[0];
   const f=r.formal_mapping,module=data.modules.find(m=>m.name===principal.module);
   if(await bytes.data!==s.reg.graph.data_sha256||await bytes.mathematics!==s.reg.graph.mathematics_sha256||mapping.result!==f.result_key||principal.signature!==f.signature||principal.source!==f.source_file||module?.sha256.toLowerCase()!==f.source_sha256||f.source_commit!==s.reg.repository.commit||f.mathematics_json_sha256!==s.reg.graph.mathematics_sha256)throw Error('Formal binding');
   await X.fresh(s,r);if(serial!==ticket)return null;pending=null;current={ticket,n,r,s,principal,kind:mapping.role};return current;
  }catch{return null;}
 }
 const isCurrent=c=>c===current&&c?.ticket===serial;
 async function render(host,context,view){host.replaceChildren();if(!isCurrent(context))return;try{await X.fresh(context.s,context.r);if(!isCurrent(context)||!host.isConnected)return;X.render(host,context.r,view);}catch{if(isCurrent(context))clear();}}
 async function navigate(context){if(!isCurrent(context))return;try{await X.fresh(context.s,context.r);if(isCurrent(context))navigateExplanation(context.principal.id);}catch{if(isCurrent(context))clear();}}
 let suspended=null;
 function suspend(){if(current)suspended={node:current.n,view:document.querySelector('#detail [role=tab][aria-selected=true]')?.textContent};else if(pending)suspended=pending;clear();}
 function resume(){const saved=current?{node:current.n,view:document.querySelector('#detail [role=tab][aria-selected=true]')?.textContent}:suspended;suspended=null;if(saved&&document.getElementById('detail')?.dataset.inspector!=='source'){clear();showDeclaration(saved.node,saved.view);}}
 document.addEventListener('visibilitychange',()=>{if(document.hidden)suspend();else resume();});window.addEventListener('pageshow',e=>{if(e.persisted)resume();});window.addEventListener('focus',resume);window.addEventListener('offline',suspend);
 return {loaded,clear,selection,render,navigate,isCurrent};
})();
