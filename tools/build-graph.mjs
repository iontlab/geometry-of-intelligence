import fs from 'node:fs';
import crypto from 'node:crypto';
const root = new URL('../', import.meta.url);
const modules = ['FourStateQuotient','CapabilityOrder','SymmetryObstruction','TransformationSufficientQuotient'];
const hashes = ['CB7132277F70879040917C06EE0CD1D9508438C1C543D5130156195F17FC8482','D3C5E69AD2C7BDB14C3FDDD1B39388AA8D24502DFE91D600E73EF8CC41DDE1D9','B17E16126A44018F1D44A24A40BD58B7607829D8537857DA77CAE167766A2351','E04891B0FB52C7A9E6C7A67A35006A3D4C428B0E80119001CDAF649BD93858C3'];
const metadata = new Map();
for (const [i,mod] of modules.entries()) {
  const file = `ILab/RQ001/${mod}.lean`;
  const bytes = fs.readFileSync(new URL(file,root));
  const hash = crypto.createHash('sha256').update(bytes).digest('hex').toUpperCase();
  if(hash !== hashes[i]) throw new Error(`Verified source changed: ${file}`);
  const source = bytes.toString('utf8');
  if(/\b(sorry|admit|axiom|native_decide|sorryAx)\b/.test(source)) throw new Error(`Prohibited token: ${file}`);
  for(const match of source.matchAll(/^(?:@\[[^\n]*?\]\s*)?(structure|inductive|def|abbrev|instance|theorem|lemma)\s+(\w+)/gm)) {
    const name = `ILab.RQ001.${match[2]}`;
    metadata.set(name,{source:file,line:source.slice(0,match.index).split('\n').length,sourceKind:match[1]});
  }
}
const raw = JSON.parse(fs.readFileSync(new URL('docs/formalization/rq001/compiled.json',root),'utf8'));
const ids = new Set(raw.map(n=>n.id));
const allowed = new Set(['propext','Classical.choice','Quot.sound']);
const sourceRef = process.env.SOURCE_REF || 'main';
const mappings = {
  FourStateQuotient:'M3.1 — four-state task/update-aware refinement; M3.2 — failure of descent. Exact task/full quotient cardinality equations are not separate named Lean theorems.',
  CapabilityOrder:'M1.1 — capability preorder / quotient structure; part of M1.2 — monotonicity implies extensionality only.',
  SymmetryObstruction:'M5.1 — transitive-action invariant-subset obstruction.',
  TransformationSufficientQuotient:'M4.1 — transformation-sufficient quotient functor and full universal property.'
};
for(const n of raw) {
  if(!n.id.startsWith('ILab.RQ001.')) throw new Error('Out-of-scope node');
  if(n.axioms.some(a=>!allowed.has(a))) throw new Error(`Unexpected axiom: ${n.id}`);
  if(n.dependencies.some(d=>!ids.has(d))) throw new Error(`Unresolved local dependency: ${n.id}`);
  const meta = metadata.get(n.id);
  const ancestor = [...metadata.entries()].filter(([id])=>n.id.startsWith(id+'.')).sort((a,b)=>b[0].length-a[0].length)[0]?.[1];
  n.authored = !!meta;
  n.source = meta?.source || ancestor?.source || n.module.replaceAll('.','/')+'.lean';
  n.line = meta?.line || ancestor?.line || null;
  n.lineProvenance = meta ? 'authored declaration start, matched against verified source' : ancestor ? 'enclosing authored declaration' : 'not available';
  if(meta?.sourceKind === 'instance') n.kind='instance';
  if(meta?.sourceKind === 'structure') n.kind='structure';
  n.sourceKind=meta?.sourceKind || null;
  n.sourceUrl=`https://github.com/iontlab/geometry-of-intelligence/blob/${sourceRef}/${n.source}${n.line?'#L'+n.line:''}`;
  n.paperMapping={provenance:'Human-authored module-level mapping, not a formal dependency or a separate proof claim for every helper',text:mappings[n.module.split('.').at(-1)] || 'No authored paper mapping'};
  n.verification='Compiled and axiom-audited in the pinned public project';
}
for(const id of metadata.keys()) if(!ids.has(id)) throw new Error(`Authored declaration absent from environment: ${id}`);
const data = {
  schemaVersion:1,
  title:'RQ-001 Phase I — Lean Formalization',
  scope:'Selected mathematical results from RQ-001 Phase I are Lean-verified. This is a partial formalization of the mathematical core, not a formalization of RQ-001 as a whole.',
  disclaimer:'The graph displays formal declaration dependencies and verification metadata. Graph position or centrality does not indicate mathematical importance, novelty, or intelligence relevance.',
  lean:'4.34.0',leanCommit:'293d5d0c0c3f3dded4688b3ccd6a33939ac5102b',mathlib:'v4.34.0',mathlibRevision:'5ed2965256430c3649e86755f9576b54eca72435',
  extraction:'Direct constant references in compiled declaration types and values; no transitive reduction, conceptual edges, or bridging across hidden nodes. Generated declarations are hidden by default. Mathlib/external references are excluded.',
  sourceRef, modules:modules.map((m,i)=>({name:'ILab.RQ001.'+m,sha256:hashes[i],paperMapping:mappings[m]})),
  nodes:raw, edges:raw.flatMap(n=>n.dependencies.map(d=>({source:n.id,target:d,kind:'direct Lean dependency'})))
};
fs.writeFileSync(new URL('docs/formalization/rq001/data.json',root),JSON.stringify(data,null,2)+'\n');
fs.writeFileSync(new URL('formalization/rq001/verification/source-hashes.json',root),JSON.stringify(data.modules,null,2)+'\n');
console.log(`PASS: ${raw.length} compiled declarations; ${metadata.size} authored nodes; ${data.edges.length} direct project-local edges; all source hashes and axiom dependencies checked.`);
