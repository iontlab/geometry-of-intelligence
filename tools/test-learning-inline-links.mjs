// Exercise the production wiki adapter with an isolated DOM and source-check fixture.
// Server authorization, revision and hash checks are separately tested by test-learning-plugin.php.
import fs from 'node:fs';
import vm from 'node:vm';
import assert from 'node:assert/strict';
const code=fs.readFileSync(new URL('../docs/formalization/mathematics-learning/explanations/wiki-adapter.js',import.meta.url),'utf8');
const pageId='mathematics_learning:higher_category_theory:synthetic_category_theory:size';
const base='https://iontlab.org/doku.php?id='+pageId;
const pause=()=>new Promise(resolve=>setImmediate(resolve));
const deferred=()=>{let resolve;const promise=new Promise(r=>resolve=r);return {promise,resolve};};
async function fixture(options={}){
 const listeners=new Map(),events=[];
 class Node {
  constructor(tag,text=''){this.tagName=tag;this.textContent=text;this.children=[];this.attrs={};this.nodeType=1;this.isConnected=true;}
  append(...nodes){for(const n of nodes){n.parentElement=this;n.isConnected=true;this.children.push(n);}}
  after(n){const a=this.parentElement.children;n.parentElement=this.parentElement;a.splice(a.indexOf(this)+1,0,n);}
  before(n){const a=this.parentElement.children;n.parentElement=this.parentElement;a.splice(a.indexOf(this),0,n);}
  setAttribute(k,v){this.attrs[k]=v;}
  getAttribute(k){return this.attrs[k];}
  closest(s){if(s==='.page')return page;if(s==='.ilab-explain')return this.className?.includes('ilab-explain')?this:this.parentElement?.closest(s);return null;}
  remove(){this.isConnected=false;for(const n of this.children)n.remove();if(this.parentElement)this.parentElement.children=this.parentElement.children.filter(n=>n!==this);}
  focus(){events.push('focus');}
  scrollIntoView(){events.push('scroll:'+this.id);}
  click(){return this.onclick?.();}
  querySelector(s){if(s==='script[type="text/tikz"],svg animate')return options.diagramsPending?{}:null;return this.querySelectorAll(s)[0]||null;}
  querySelectorAll(s){const id=s.match(/^\[id="(.+)"\]$/)?.[1];return this.children.flatMap(n=>[...(n.id===id?[n]:[]),...n.querySelectorAll(s)]);}
  addEventListener(type,fn){listeners.set('page:'+type,fn);}
  removeEventListener(type){listeners.delete('page:'+type);}
 }
 const page=new Node('div'),heading=new Node('h3','Definition 1.1.'),binding=new Node('script');heading.id='definition_11';page.append(heading,binding);
 const record={wiki:true,object_key:'explain.mathematics-learning.source.1.1',source:{page_id:pageId,item_key:'1.1',item_label:'Definition 1.1',anchor:heading.id,heading_text:heading.textContent}};
 const token={page_id:pageId,revision:1,raw_sha256:'raw',fragment_sha256:'fragment',role:'anonymous',registry_sha256:'registry',release:'release',render_contract:'contract',keys:[record.object_key],...options.token};
 binding.textContent=JSON.stringify(token);
 const state={reg:{records:[record]},release:{registry_sha256:'registry',release:'release',render_contract:'contract'},contract:{pages:{[pageId]:{revision:1,raw_sha256:'raw',fragments:{anonymous:['fragment']}}}}};
 let observer,freshCount=0,renderCount=0;
 const window={MathJax:{startup:{promise:options.math?.promise||Promise.resolve()}},addEventListener:(type,fn)=>listeners.set(type,fn)};
 const document={getElementById:()=>binding,hidden:false,addEventListener:(type,fn)=>listeners.set(type,fn)};
 const location={href:options.url||base+'&ilab_explain=1.1&view=plain#definition_11'};
 const X={element:(tag,text)=>new Node(tag,text),load:async()=>state,fresh:async()=>{freshCount++;if(options.stale)throw Error('Stale binding');},tabs(names,bar,activate,prefix){
  const bs=names.map((name,i)=>{const b=new Node('button',name);b.id=prefix+'-tab-'+i;b.onclick=()=>{bs.forEach((b,j)=>b.setAttribute('aria-selected',String(j===i)));activate(name,b.id);};bar.append(b);return b;});bs[0].click();return bs;
 }};
 const S={render:async(body,r,view,st,current)=>{if(options.renderGate)await options.renderGate.promise;if(current()){body.textContent=view;renderCount++;events.push('render:'+view);}}};
 window.ILabExplain=X;window.ILabLearningStatement=S;
 const context={window,document,location,URL,setTimeout,clearTimeout,console:{warn(){}},MutationObserver:class{constructor(fn){observer=fn;}observe(){}}};
 const initialized=vm.runInNewContext(code,context);
 const all=()=>{const walk=n=>[n,...n.children.flatMap(walk)];return walk(page);};
 return {initialized,options,events,location,document,heading,all,fresh:()=>freshCount,renders:()=>renderCount,controls:()=>all().filter(n=>n.textContent==='Explain Definition 1.1'),panels:()=>all().filter(n=>n.className==='ilab-explain ilab-explain-panel'),body:()=>all().find(n=>n.attrs.role==='tabpanel'),fire:async(type)=>{await listeners.get(type)?.();await pause();},finishDiagrams:()=>{options.diagramsPending=false;listeners.get('page:tikzjax-load-finished')?.();},mutate:()=>observer([{type:'characterData',target:heading}])};
}
let count=0;
async function test(name,run){await run();count++;console.log('PASS '+name);}
for(const [key,name] of Object.entries({plain:'Plain',story:'Story',mathematics:'Mathematics',lean:'Lean',verification:'Verification'})){
 await test('fresh URL selects '+name,async()=>{const f=await fixture({url:base+'&ilab_explain=1.1&view='+key+'#definition_11'});await f.initialized;assert.equal(f.body().textContent,name);assert.equal(f.panels().length,1);assert(f.fresh()>=3);assert.equal(f.events.at(-1),'scroll:definition_11');assert(f.events.indexOf('render:'+name)<f.events.indexOf('scroll:definition_11'));});
}
await test('manual button keeps the existing Mathematics default',async()=>{const f=await fixture({url:base});await f.initialized;assert.equal(f.panels().length,0);await f.controls()[0].click();assert.equal(f.body().textContent,'Mathematics');assert(!f.events.some(e=>e.startsWith('scroll:')));});
for(const query of ['ilab_explain=missing&view=plain','ilab_explain=1.1&view=unknown','ilab_explain=1.1&view=__proto__','ilab_explain=1.1','view=story']){
 await test('reject invalid selector '+query,async()=>{const f=await fixture({url:base+'&'+query});await f.initialized;assert.equal(f.panels().length,0);assert.equal(f.controls().length,1);});
}
for(const token of [{revision:2},{raw_sha256:'changed'},{fragment_sha256:'changed'},{registry_sha256:'changed'},{release:'changed'},{render_contract:'changed'},{role:'reader'},{keys:['wrong']}]){
 await test('reject attestation mismatch '+Object.keys(token)[0],async()=>{const f=await fixture({token});await f.initialized;assert.equal(f.controls().length,0);assert.equal(f.panels().length,0);});
}
await test('wait for MathJax and TikZ before initialization',async()=>{const math=deferred();const f=await fixture({math,diagramsPending:true});await pause();assert.equal(f.controls().length,0);math.resolve();await pause();assert.equal(f.controls().length,0);f.finishDiagrams();await f.initialized;assert.equal(f.body().textContent,'Plain');});
await test('wait for selected layer rendering before scrolling',async()=>{const renderGate=deferred();const f=await fixture({renderGate});await pause();assert(!f.events.some(e=>e.startsWith('scroll:')));renderGate.resolve();await f.initialized;assert.equal(f.events.at(-1),'scroll:definition_11');});
await test('stale freshness fails closed',async()=>{const f=await fixture({stale:true});await f.initialized;assert.equal(f.controls().length,0);assert.equal(f.panels().length,0);});
await test('later stale binding revokes the panel and disables controls',async()=>{const f=await fixture();await f.initialized;f.options.stale=true;await f.controls()[0].click();assert.equal(f.panels().length,0);assert(f.controls()[0].disabled);});
await test('history navigation selects an existing layer',async()=>{const f=await fixture();await f.initialized;f.location.href=base+'&ilab_explain=1.1&view=story#definition_11';await f.fire('popstate');assert.equal(f.body().textContent,'Story');assert.equal(f.panels().length,1);});
await test('anchor navigation reopens the requested inline panel',async()=>{const f=await fixture();await f.initialized;await f.all().find(n=>n.textContent==='Close').click();assert.equal(f.panels().length,0);await f.fire('hashchange');assert.equal(f.body().textContent,'Plain');});
await test('unrelated chapter anchors keep normal navigation',async()=>{const f=await fixture();await f.initialized;const before=f.events.length;f.location.href=base+'&ilab_explain=1.1&view=plain#remark_12';await f.fire('hashchange');assert.equal(f.events.length,before);f.location.href=base+'&ilab_explain=1.1&view=plain#definition_11';await f.fire('hashchange');assert.equal(f.events.at(-1),'scroll:definition_11');});
await test('returning to the page rechecks the binding and restores a deep link',async()=>{const f=await fixture();await f.initialized;f.document.hidden=true;await f.fire('visibilitychange');assert.equal(f.panels().length,0);f.document.hidden=false;await f.fire('visibilitychange');assert.equal(f.body().textContent,'Plain');});
await test('source mutation permanently revokes auto and manual opening',async()=>{const f=await fixture();await f.initialized;f.mutate();await f.fire('pageshow');await f.fire('hashchange');assert.equal(f.panels().length,0);assert(f.controls()[0].disabled);});
console.log(`${count} inline-navigation and fail-closed checks passed.`);
