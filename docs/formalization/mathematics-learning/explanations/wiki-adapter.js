/* Learning scope of the deployed RQ-001 panel pattern. Requires exact server attestation. */
'use strict';
(async()=>{
 const X=window.ILabExplain,S=window.ILabLearningStatement,binding=document.getElementById('ilab-learning-binding');
 if(!X||!S||!binding)return;
 let panel,trigger,generation=0,valid=true,mutated=false;const controls=[],openers=[];
 const close=(focus=false)=>{generation++;panel?.remove();panel=null;if(focus&&trigger?.isConnected)trigger.focus({preventScroll:true});};
 const revoke=()=>{valid=false;close();controls.forEach(c=>c.disabled=true);};
 try{
  const token=JSON.parse(binding.textContent),state=await X.load(),contract=state.contract.pages[token.page_id];
  const records=state.reg.records.filter(r=>r.wiki===true&&r.source.page_id===token.page_id);
  if(!contract||token.revision!==contract.revision||token.raw_sha256!==contract.raw_sha256||token.render_contract!==state.release.render_contract||token.registry_sha256!==state.release.registry_sha256||token.release!==state.release.release||!contract.fragments?.[token.role]?.includes(token.fragment_sha256)||JSON.stringify(token.keys)!==JSON.stringify(records.map(r=>r.object_key)))return;
  await X.fresh(state,records[0]);
  if(window.MathJax?.startup?.promise)await window.MathJax.startup.promise;
  const page=binding.closest('.page');if(!page)return;
  // TikZJax replaces each source script with a temporary SVG, then its final SVG.
  // Wait for that renderer before installing the immutable-content observer.
  const diagramsPending=()=>page.querySelector('script[type="text/tikz"],svg animate');
  if(diagramsPending())await new Promise((resolve,reject)=>{
   const done=()=>{if(!diagramsPending()){clearTimeout(timer);page.removeEventListener('tikzjax-load-finished',done);resolve();}};
   const timer=setTimeout(()=>{page.removeEventListener('tikzjax-load-finished',done);reject(Error('Diagram rendering did not finish'));},60000);
   page.addEventListener('tikzjax-load-finished',done);done();
  });
  const targets=records.map(r=>{
   const hs=page.querySelectorAll('[id="'+r.source.anchor+'"]');
   if(hs.length!==1||hs[0].textContent!==r.source.heading_text)throw Error('Statement anchor changed');return hs[0];
  });
  for(const [i,r] of records.entries()){
   // Preserve previous links where an original source title replaces an editorial title.
   const legacy=r.source.legacy_anchor;
   if(legacy&&legacy!==r.source.anchor&&!page.querySelector('[id="'+legacy+'"]')){
    const alias=X.element('span');alias.id=legacy;alias.setAttribute('aria-hidden','true');targets[i].before(alias);
   }
   const wrap=X.element('div');wrap.className='ilab-explain';
   const b=X.element('button','Explain '+r.source.item_label);b.type='button';wrap.append(b);targets[i].after(wrap);controls.push(b);
   const open=async(view='Mathematics',navigate=false)=>{close();trigger=b;const ticket=++generation;
    try{if(!valid)return;await X.fresh(state,r);if(ticket!==generation||!valid)return;
     panel=X.element('section');panel.className='ilab-explain ilab-explain-panel';panel.setAttribute('role','region');panel.setAttribute('aria-label','Explanation: '+r.source.heading_text);panel.tabIndex=-1;
     const bar=X.element('div'),body=X.element('div'),exit=X.element('button','Close');exit.type='button';exit.onclick=()=>close(true);body.id='ilab-learning-pane';body.setAttribute('role','tabpanel');body.tabIndex=0;
     panel.append(bar,exit,body);wrap.after(panel);
     let ready;
     const names=['Mathematics','Plain','Story','Lean','Verification'];
     const tabs=X.tabs(names,bar,(name,id)=>{
      body.setAttribute('aria-labelledby',id);const selected=++generation;
      ready=(async()=>{
       try{await X.fresh(state,r);if(!valid||selected!==generation)return;await S.render(body,r,name,state,()=>valid&&selected===generation&&body.isConnected);}catch(error){console.warn('Learning explanation could not be verified',error);if(selected===generation)revoke();}
      })();
     },'ilab-learning');
     if(view!=='Mathematics')tabs[names.indexOf(view)].click();
     const selected=generation;await ready;
     if(!valid||selected!==generation||!body.isConnected)return;
     panel.focus({preventScroll:true});
     if(navigate)targets[i].scrollIntoView({block:'start',behavior:'auto'});
    }catch{revoke();}
   };
   b.onclick=()=>open();openers.push(open);
  }
  // URL input selects only an already verified source record and existing tab.
  // No URL parameter can supply content, a source revision, or a binding override.
  async function openRequested(){
   if(!valid)return;
   const url=new URL(location.href),params=url.searchParams;
   if(!params.has('ilab_explain'))return;
   const views={plain:'Plain',story:'Story',mathematics:'Mathematics',lean:'Lean',verification:'Verification'};
   const index=records.findIndex(r=>r.source.item_key===params.get('ilab_explain'));
   const key=params.get('view');
   if(params.get('id')!==token.page_id||index<0||!Object.hasOwn(views,key)){close();return;}
   // A reader following a different chapter anchor must remain at that anchor.
   if(url.hash&&url.hash!=='#'+records[index].source.anchor)return;
   await openers[index](views[key],true);
  }
  new MutationObserver(ms=>{
   // MathJax can edit a text node and then detach it in the same observer batch.
   // Its former panel parent remains identifiable in that batch's removal record.
   const panelRemovals=ms.filter(m=>m.type==='childList'&&m.target.nodeType===1&&m.target.closest('.ilab-explain')).flatMap(m=>[...m.removedNodes]);
   if(ms.some(m=>{
   if(!m.target.isConnected&&panelRemovals.some(n=>n===m.target||n.contains(m.target)))return false;
   const e=m.target.nodeType===1?m.target:m.target.parentElement;
   if(e?.closest('.ilab-explain'))return false;
   if(m.type==='attributes'&&e?.closest('#dw__toc')&&['class','style','aria-expanded'].includes(m.attributeName))return false;
   if(e?.closest('#dw__toc h3.toggle'))return false;
   const changed=m.type!=='childList'||[...m.addedNodes,...m.removedNodes].some(n=>!(n.nodeType===1&&n.matches('.ilab-explain')));
   if(changed)console.warn('Learning source changed after verification',m.type,m.attributeName);
   return changed;
  })){mutated=true;revoke();}}).observe(page,{subtree:true,childList:true,characterData:true,attributes:true});
  document.addEventListener('visibilitychange',()=>{if(document.hidden)revoke();else resume();});window.addEventListener('pageshow',resume);window.addEventListener('focus',resume);window.addEventListener('offline',revoke);
  window.addEventListener('popstate',openRequested);window.addEventListener('hashchange',openRequested);
  async function resume(){revoke();const ticket=generation;try{await X.fresh(state,records[0]);if(mutated||ticket!==generation)return;valid=true;controls.forEach(c=>c.disabled=false);await openRequested();}catch{}}
  await openRequested();
 }catch{revoke();}
})();
