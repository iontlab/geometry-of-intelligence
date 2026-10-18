import fs from 'node:fs';
import crypto from 'node:crypto';
const root = new URL('../', import.meta.url);
const audit = JSON.parse(fs.readFileSync(new URL('formalization/mathematics-learning/verification/expanded-audit.json',root),'utf8'));
const modules = audit.modules.map(m=>m.name.split('.').at(-1));
const hashes = audit.modules.map(m=>m.sha256.toUpperCase());
const compiledBytes = fs.readFileSync(new URL('docs/formalization/mathematics-learning/compiled.json',root));
if(crypto.createHash('sha256').update(compiledBytes).digest('hex')!==audit.compiled_sha256)throw new Error('Compiled audit changed');
const metadata = new Map();
for (const [i,mod] of modules.entries()) {
  const file = `ILab/MathematicsLearning/${mod}.lean`;
  const bytes = fs.readFileSync(new URL(file,root));
  const hash = crypto.createHash('sha256').update(bytes).digest('hex').toUpperCase();
  if(hash !== hashes[i]) throw new Error(`Verified source changed: ${file}`);
  const source = bytes.toString('utf8');
  // Compiler auditing is authoritative. This additional source check ignores prose comments.
  const code=source.replace(/\/-[\s\S]*?-\//g,'').replace(/--[^\n]*/g,'');
  if(/\b(sorry|admit|axiom|native_decide|sorryAx)\b/.test(code)) throw new Error(`Prohibited token: ${file}`);
  for(const match of source.matchAll(/^(?:@\[[^\n]*?\]\s*)?(?:noncomputable\s+)?(structure|inductive|def|abbrev|instance|theorem|lemma)\s+(\w+)/gm)) {
    const name = `ILab.MathematicsLearning.${match[2]}`;
    metadata.set(name,{source:file,line:source.slice(0,match.index).split('\n').length,sourceKind:match[1]});
  }
}
const raw = JSON.parse(fs.readFileSync(new URL('docs/formalization/mathematics-learning/compiled.json',root),'utf8'));
const ids = new Set(raw.map(n=>n.id));
const allowed = new Set(['propext','Classical.choice','Quot.sound']);
const sourceRef = process.env.SOURCE_REF;
if (!/^[0-9a-f]{40}$/.test(sourceRef || '')) throw new Error('SOURCE_REF must be the exact verified source commit');
const mappings = {
  BasicCategoryTheory:'Primary 1.5 and 1.11: non-exercise identity laws and inverse uniqueness. Assigned exercise solutions are withheld.',
  WalkingIsomorphism:'Primary 1.25, 3.4, 3.8 and 3.9: one-object and two-object singleton-hom categories, an explicit adjoint equivalence and two-object cardinality.',
  SetUniverses:'Primary 1.1–1.4: ZFSet universe closure assumptions and consequences. Introduction: equality substitution and transport. Universe existence is assumed, not proved.',
  CategoryConstructions:'Primary 1.5–1.13, 1.18, 1.20, 1.22, 3.2 and 3.5: ordinary definitions, examples and supplied laws. Assigned construction checks are withheld.',
  CategorySize:'Primary 1.4, 1.8 and 1.16: type-universe size and local smallness. These are explicitly scoped type-theoretic formulations, not a literal ZFSet encoding of all categories.',
  YonedaAdjunction:'Primary 2.3, the non-assigned part of 2.6, 2.7, 3.1 and 3.4–3.7: definitions, non-exercise consequences and equivalence criterion. Assigned Yoneda/adjunction correspondence proofs are withheld.',
  TerminalCategory:'Primary 1.25, 1.27, 3.8 and 3.9: terminal category and finite example. The strict evaluation isomorphism assigned in 1.26 is withheld.',
  PathAndIdentity:'Introduction: endpoint-fixed path homotopies, their ordinary fundamental groupoid, and group invariants. This does not construct the full infinity-groupoid or prove univalence.',
  SourceLaws:'Primary 1.9, 1.18, 3.1 and 3.6: definitions and their supplied laws; no assigned exercise construction checks.'
};
for(const n of raw) {
  if(!n.id.startsWith('ILab.MathematicsLearning.')) throw new Error('Out-of-scope node');
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
  n.paperMapping={provenance:'Independently authored module-level educational mapping, not a formal dependency or a separate proof claim for every helper',text:mappings[n.module.split('.').at(-1)] || 'No authored lesson mapping'};
  n.verification='Compiled and axiom-audited in the pinned public project';
}
for(const id of metadata.keys()) if(!ids.has(id)) throw new Error(`Authored declaration absent from environment: ${id}`);
const data = {
  schemaVersion:1,
  title:'Mathematics Learning — Ordinary Category Theory',
  scope:'Non-exercise ordinary-category material and explicit foundational formulations are checked. Assigned exercise solutions are withheld. The complete source inventory records formulation limits; full higher/synthetic foundations and universe existence are not proved.',
  disclaimer:'The graph displays formal declaration dependencies and verification metadata. Graph position or centrality does not indicate mathematical importance, novelty, or intelligence relevance.',
  lean:'4.34.0',leanCommit:'293d5d0c0c3f3dded4688b3ccd6a33939ac5102b',mathlib:'v4.34.0',mathlibRevision:'5ed2965256430c3649e86755f9576b54eca72435',
  extraction:'Direct constant references in compiled declaration types and values; no transitive reduction, conceptual edges, or bridging across hidden nodes. Generated declarations are hidden by default. Mathlib/external references are excluded.',
  sourceRef, modules:modules.map((m,i)=>({name:'ILab.MathematicsLearning.'+m,sha256:hashes[i],paperMapping:mappings[m]})),
  nodes:raw, edges:raw.flatMap(n=>n.dependencies.map(d=>({source:n.id,target:d,kind:'direct Lean dependency'})))
};
const mathematics = JSON.parse(fs.readFileSync(new URL('docs/formalization/mathematics-learning/mathematics.json',root),'utf8'));
for(const [id,m] of Object.entries(mathematics.declarations)) {
  if(!ids.has(id) || !metadata.has(id)) throw new Error(`Unknown authored mathematics declaration: ${id}`);
  if(!mathematics.results[m.result]) throw new Error(`Unknown mathematics result: ${id}`);
}
fs.writeFileSync(new URL('docs/formalization/mathematics-learning/data.json',root),JSON.stringify(data,null,2)+'\n');
fs.writeFileSync(new URL('formalization/mathematics-learning/verification/source-hashes.json',root),JSON.stringify(data.modules,null,2)+'\n');
console.log(`PASS: ${raw.length} compiled declarations; ${metadata.size} authored nodes; ${data.edges.length} direct project-local edges; all source hashes and axiom dependencies checked.`);
