/* Shared prose-only renderer. No HTML or math evaluation. */
'use strict';
window.ILabExplain = (() => {
  const base=new URL('.',document.currentScript.src).pathname, notice='Private preview — AI-authored explanations; human editorial review pending. Public release remains disabled.';
  const sha=async b=>Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256',b))).map(x=>x.toString(16).padStart(2,'0')).join('');
  const element=(tag,text)=>{const e=document.createElement(tag);if(text!==undefined)e.textContent=text;return e;};
  const text=s=>typeof s==='string'&&s.length>0&&s.length<=12000;
  function sourceURL(s) {
    if(!text(s))throw Error('Missing source');const u=new URL(s,location.origin);
    if(u.protocol!=='https:'||u.username||u.password||!['iontlab.org','github.com'].includes(u.hostname))throw Error('Unsafe source');
    if(u.hostname==='iontlab.org'&&(u.pathname!=='/doku.php'||!/^mathematics_learning:higher_category_theory:synthetic_category_theory:[a-z_]+$/.test(u.searchParams.get('id')||'')||!/^\d+$/.test(u.searchParams.get('rev')||'')))throw Error('Unpinned source');
    if(u.hostname==='github.com'&&!/^\/iontlab\/geometry-of-intelligence\/blob\/[a-f0-9]{40}\/ILab\/MathematicsLearning\/[A-Za-z]+\.lean$/.test(u.pathname))throw Error('Unpinned formal source');
    return u.href;
  }
  function validate(reg) {
    function depth(x,n=0){if(n>16)throw Error('Depth');if(typeof x==='string'&&x.length>20000)throw Error('Length');if(x&&typeof x==='object'){if(Object.keys(x).length>200)throw Error('Size');Object.values(x).forEach(v=>depth(v,n+1));}}depth(reg);
    if(reg.schema_version!=='explanation-content-draft-1'||reg.content_format?.version!=='plain-text-blocks-1'||!Array.isArray(reg.records)||reg.records.length<1||reg.records.length>200)throw Error('Schema');
    const keys=new Set(); const blocks=b=>Array.isArray(b)&&b.length>0&&b.length<=50&&b.every(x=>x.type==='paragraph'&&text(x.text)&&Object.keys(x).length===2);
    const prefix='explain.mathematics-learning.';
    for(const r of reg.records){const c=r.content;
      if(!r.object_key?.startsWith(prefix)||keys.has(r.object_key)||r.locale!=='en'||!text(c?.plain?.title)||!blocks(c.plain.blocks)||!text(c.story?.title)||c.story.label!=='Story analogy'||c.story.disclaimer!=='This story is an analogy, not the mathematical statement or proof.'||!blocks(c.story.blocks)||!blocks(c.where_analogy_stops)||!Array.isArray(c.story_key)||!c.story_key.length||c.story_key.length>30||!c.story_key.every(x=>text(x.story_element)&&text(x.scientific_counterpart)&&Object.keys(x).length===2))throw Error('Record');
      sourceURL(r.source.source_link);if(r.formal_mapping.declaration)sourceURL(r.formal_mapping.pinned_source_link);keys.add(r.object_key);
    }return reg;
  }
  async function json(path){const r=await fetch(path,{cache:'no-store',signal:AbortSignal.timeout(5000)});if(!r.ok)throw Error('Asset unavailable');const b=await r.arrayBuffer();if(b.byteLength>500000)throw Error('Asset size');return {value:JSON.parse(new TextDecoder('utf-8',{fatal:true}).decode(b)),hash:await sha(b)};}
  // User-authorized publication is distinct from independent editorial review.
  function permitted(reg,release){return release.enabled===true&&release.publication_authorized===true&&reg.release.enabled===true&&reg.release.publication_authorized===true&&reg.records.every(r=>r.release_ready===true&&r.review.status==='AI-authored; independent human review not claimed');}
  let statePromise;
  async function load(){if(!statePromise)statePromise=(async()=>{
    const [a,b,c]=await Promise.all([json(base+'registry.v0.1.json'),json(base+'release.json'),json(base+'binding.json')]);
    const reg=validate(a.value),release=b.value,contract=c.value;
    if(a.hash!==release.registry_sha256||!permitted(reg,release)||contract.render_contract!==release.render_contract)throw Error('Release unavailable');
    if(!reg.records.every(r=>{const p=contract.pages[r.source.page_id];return p&&r.source.revision===p.revision&&r.source.whole_page_sha256===p.raw_sha256;}))throw Error('Source tuple mismatch');
    return {reg,release,contract,preview:false};
  })();return statePromise;}
  async function fresh(state,record){
    if(!record)throw Error('Missing source binding');
    const {value:release}=await json(base+'release.json');
    if(!permitted(state.reg,release)||release.registry_sha256!==state.release.registry_sha256||release.release!==state.release.release)throw Error('Release changed');
    const page=record.source.page_id, binding=state.contract.pages[page];
    const local=['localhost','127.0.0.1','[::1]'].includes(location.hostname);
    if(!local){
      if(state.contract.freshness_endpoint!=='ilabexplain_learning_status')throw Error('Missing authoritative freshness endpoint');
      const nonce=Array.from(crypto.getRandomValues(new Uint8Array(16))).map(x=>x.toString(16).padStart(2,'0')).join('');
      const {value:s}=await json('/lib/exe/ajax.php?call=ilabexplain_learning_status&id='+encodeURIComponent(page)+'&nonce='+nonce);
      if(s.available!==true||s.nonce!==nonce||s.page_id!==page||s.revision!==binding.revision||s.raw_sha256!==binding.raw_sha256||s.release!==state.release.release||s.registry_sha256!==state.release.registry_sha256)throw Error('Stale source');
      return true;
    }
    // Local fixtures are used only by the isolated preview server.
    const url=base+'fixtures/'+page.split(':').at(-1)+'.txt';
    const response=await fetch(url,{cache:'no-store',signal:AbortSignal.timeout(5000)});
    if(!response.ok||await sha(await response.arrayBuffer())!==binding.raw_sha256)throw Error('Stale source');
    return true;
  }
  function render(host,r,view){
    host.replaceChildren();host.classList.add('ilab-explain');
    const c=r.content,layer=view==='Story'?c.story:c.plain;
    host.append(element('h4',layer.title));
    if(view==='Story')host.append(element('p',c.story.label),element('p',c.story.disclaimer));
    layer.blocks.forEach(b=>host.append(element('p',b.text)));
    if(view==='Story'){
      host.append(element('h4','Story key'));const dl=element('dl');
      c.story_key.forEach(row=>dl.append(element('dt',row.story_element),element('dd',row.scientific_counterpart)));host.append(dl,element('h4','Where the analogy stops'));
      c.where_analogy_stops.forEach(b=>host.append(element('p',b.text)));
    }
    const a=element('a','Exact scientific source · pinned edition ↗');a.href=sourceURL(r.source.source_link);host.append(a);
    if(r.formal_mapping.declaration){const p=element('p',r.formal_mapping.scope_note);const a=element('a','Underlying formal source · pinned commit ↗');a.href=sourceURL(r.formal_mapping.pinned_source_link);host.append(p,a);}
  }
  function tabs(names,container,activate,prefix){
    container.setAttribute('role','tablist');container.setAttribute('aria-label','Explanation views');
    const bs=names.map((name,i)=>{const b=element('button',name);b.type='button';b.id=prefix+'-tab-'+i;b.setAttribute('role','tab');b.setAttribute('aria-controls',prefix+'-pane');b.onclick=()=>choose(i);b.onkeydown=e=>{let n={ArrowRight:(i+1)%names.length,ArrowLeft:(i+names.length-1)%names.length,Home:0,End:names.length-1}[e.key];if(n!==undefined){e.preventDefault();choose(n);bs[n].focus();}};container.append(b);return b;});
    function choose(i){bs.forEach((b,j)=>{b.tabIndex=i===j?0:-1;b.setAttribute('aria-selected',String(i===j));});activate(names[i],bs[i].id);}choose(0);return bs;
  }
  return {base,notice,sha,element,validate,sourceURL,permitted,load,fresh,render,tabs};
})();
