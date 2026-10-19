import fs from 'node:fs';
import vm from 'node:vm';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';
import {performance} from 'node:perf_hooks';
const root=new URL('../docs/formalization/mathematics-learning/explanations/',import.meta.url);
const read=p=>fs.readFileSync(new URL(p,root));
const capacity=JSON.parse(read('capacity.json'));
const registry=JSON.parse(read('registry.v0.1.json'));
const release=JSON.parse(read('release.json'));
const binding=JSON.parse(read('binding.json'));
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
let cancelled=false;
const stream=(parts,header='1')=>({ok:true,headers:new Headers({'content-length':header}),body:new ReadableStream({start(c){for(const p of parts)c.enqueue(new Uint8Array(p));c.close();},cancel(){cancelled=true;}})});
function runtime(fetch){const c={window:{},document:{currentScript:{src:'https://iontlab.org/formalization/mathematics-learning/explanations/renderer.js'}},URL,location:{origin:'https://iontlab.org'},crypto:crypto.webcrypto,AbortSignal,TextDecoder,Uint8Array,fetch};vm.runInNewContext(read('renderer.js').toString(),c);return c.window.ILabExplain;}
const X=runtime();let checks=0;
function test(name,f){f();checks++;console.log('PASS:',name);}
test('shared policy accepts 5 MB',()=>assert.equal(X.validateCapacity(capacity).registry_bytes,5000000));
for(const bad of [null,{}, {...capacity,registry_bytes:'5000000'}, {...capacity,registry_bytes:50000001},{...capacity,registry_records:199},{...capacity,registry_records:1.5}])test('invalid configuration fails closed',()=>assert.throws(()=>X.validateCapacity(bad)));
test('current complete registry validates',()=>X.validate(registry,capacity));
assert.equal((await X.boundedBytes(stream([4999999,1]),5000000)).byteLength,5000000);checks++;
await assert.rejects(X.boundedBytes(stream([4999999,2,100]),5000000),/Asset size/);checks++;
test('oversized stream is cancelled despite misleading content length',()=>assert(cancelled));
const grown=structuredClone(registry);while(grown.records.length<750){const r=structuredClone(registry.records[grown.records.length%registry.records.length]);r.object_key+='.'+grown.records.length;grown.records.push(r);}
let raw=Buffer.from(JSON.stringify(grown));assert(raw.length<5000000);const padded=Buffer.concat([raw,Buffer.alloc(5000000-raw.length,32)]);
const start=performance.now();X.validate(JSON.parse(padded),capacity);const elapsed=performance.now()-start;checks++;
test('record limit remains enforced',()=>assert.throws(()=>X.validate(grown,{...capacity,registry_records:200})));
test('per-record depth limit remains enforced',()=>{const r=structuredClone(registry);let p=r;for(let i=0;i<18;i++)p=p.extra={};assert.throws(()=>X.validate(r,capacity));});
async function loadTest(overrides={}){const assets={'registry.v0.1.json':read('registry.v0.1.json'),'capacity.json':read('capacity.json'),'release.json':Buffer.from(JSON.stringify(release)),'binding.json':Buffer.from(JSON.stringify(binding)),...overrides};return runtime(async url=>new Response(assets[url.split('/').at(-1)])).load();}
await loadTest();checks++;
await assert.rejects(loadTest({'capacity.json':Buffer.from(JSON.stringify({...capacity,registry_bytes:6000000}))}),/Capacity integrity/);checks++;
await assert.rejects(loadTest({'registry.v0.1.json':Buffer.concat([read('registry.v0.1.json'),Buffer.from(' ')])}),/Release unavailable/);checks++;
const report={checks,registry_bytes:read('registry.v0.1.json').length,capacity_bytes:capacity.registry_bytes,headroom:capacity.registry_bytes-read('registry.v0.1.json').length,synthetic_bytes:padded.length,synthetic_records:grown.records.length,parse_validate_ms:elapsed,note:'Node V8 timing; browser/device/network timing is separate.'};
if(process.argv[2])fs.writeFileSync(process.argv[2],JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify(report));
