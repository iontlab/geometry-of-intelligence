import fs from 'node:fs';
import vm from 'node:vm';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';
const root=new URL('../docs/formalization/mathematics-learning/',import.meta.url);
const bytes=p=>fs.readFileSync(new URL(p,root));
const read=p=>JSON.parse(bytes(p));
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const reg=read('explanations/registry.v0.1.json'),release=read('explanations/release.json'),contract=read('explanations/binding.json'),data=read('data.json'),math=read('mathematics.json');
const context={window:{},document:{currentScript:{src:'https://iontlab.org/formalization/mathematics-learning/explanations/renderer.js'}},URL,location:{origin:'https://iontlab.org'},crypto:crypto.webcrypto};
vm.runInNewContext(bytes('explanations/renderer.js').toString(),context);
context.window.ILabExplain.validate(reg);
assert.equal(context.window.ILabExplain.permitted(reg,release),true);
assert.equal(sha(bytes('explanations/registry.v0.1.json')),release.registry_sha256);
assert.equal(sha(bytes('data.json')),reg.graph.data_sha256);
assert.equal(sha(bytes('mathematics.json')),reg.graph.mathematics_sha256);
assert.equal(sha(bytes('explanations/native-source.json')),reg.native_source_sha256);
assert.equal(math.native_source_sha256,reg.native_source_sha256);
assert.equal(reg.repository.commit,data.sourceRef);
const source=reg.records.filter(r=>r.kind==='source-item'),graph=reg.records.filter(r=>r.kind==='graph-result');
assert.equal(source.length,58);assert.equal(new Set(source.map(r=>r.source.item_key)).size,58);
assert.equal(reg.records.filter(r=>r.wiki).length,47);
assert.equal(new Set(graph.map(r=>r.formal_mapping.declaration)).size,graph.length);
const nodes=new Map(data.nodes.map(n=>[n.id,n]));
for(const r of reg.records){
 const c=contract.pages[r.source.page_id];assert.equal(r.source.revision,c.revision);assert.equal(r.source.whole_page_sha256,c.raw_sha256);
 assert.equal(sha(bytes('explanations/fixtures/'+r.source.page_id.split(':').at(-1)+'.txt')),c.raw_sha256);
 if(r.kind==='source-item'){for(const id of r.formal_mapping.declarations)assert(nodes.get(id)?.authored);continue;}
 const f=r.formal_mapping,n=nodes.get(f.declaration),m=math.declarations[n.id];
 assert(n.authored);assert.equal(m.role,'principal');assert.equal(m.result,f.result_key);assert.equal(n.signature,f.signature);assert.equal(n.source,f.source_file);
 assert.equal(data.modules.find(m=>m.name===n.module).sha256.toLowerCase(),f.source_sha256);assert.equal(f.source_commit,data.sourceRef);assert.equal(f.mathematics_json_sha256,reg.graph.mathematics_sha256);
}
assert.equal(Object.values(math.declarations).filter(m=>m.role==='principal').length,graph.length);
for(const n of data.nodes)assert.deepEqual(new Set(data.edges.filter(e=>e.source===n.id).map(e=>e.target)),new Set(n.dependencies));
console.log(`PASS: ${source.length} unique source bindings, ${graph.length} exact graph bindings, 47 inline controls, release hashes and all ${data.edges.length} compiled edges.`);
