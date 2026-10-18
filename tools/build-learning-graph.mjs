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
  const scopes=[];
  for(const [i,line] of source.split('\n').entries()) {
    const ns=line.match(/^namespace\s+([\w.]+)/);
    if(ns){scopes.push(ns[1]);continue;}
    if(/^(?:noncomputable\s+)?section(?:\s|$)/.test(line)){scopes.push('');continue;}
    if(/^end(?:\s|$)/.test(line)){scopes.pop();continue;}
    const match=line.match(/^(?:@\[[^\n]*?\]\s*)?(?:noncomputable\s+)?(structure|inductive|def|abbrev|instance|theorem|lemma)\s+([\w.]+)/);
    if(!match)continue;
    const name=[...scopes.filter(Boolean),match[2]].join('.');
    metadata.set(name,{source:file,line:i+1,sourceKind:match[1]});
  }
}
const raw = JSON.parse(fs.readFileSync(new URL('docs/formalization/mathematics-learning/compiled.json',root),'utf8'));
const ids = new Set(raw.map(n=>n.id));
const allowed = new Set(['propext','Classical.choice','Quot.sound']);
const sourceRef = process.env.SOURCE_REF;
if (!/^[0-9a-f]{40}$/.test(sourceRef || '')) throw new Error('SOURCE_REF must be the exact verified source commit');
const mappings = {
  YonedaConstruction:'Theorem 2.1, page 9: author-supplied evaluation at identity and candidate component functions on exact small-set carriers. Only defining formulas are checked; candidate naturality, mutual inverseness and naturality in c,F remain assigned. The complete Yoneda theorem is not verified here.',
  BasicCategoryTheory:'Primary 1.5 and 1.11: non-exercise identity laws and inverse uniqueness. Assigned exercise solutions are withheld.',
  WalkingIsomorphism:'Primary 1.25, 3.4, 3.8 and 3.9: one-object and two-object singleton-hom categories, an explicit adjoint equivalence and two-object cardinality.',
  SetUniverses:'Primary 1.1–1.4: ZFSet universe closure assumptions and consequences. Introduction: equality substitution and transport. Universe existence is assumed, not proved.',
  CategoryConstructions:'Primary 1.5–1.13, 1.18, 1.20, 1.22, 3.2 and 3.5: ordinary definitions, examples and supplied laws. Assigned construction checks are withheld.',
  CategorySize:'Primary 1.4, 1.8 and 1.16: type-universe size and local smallness. These are explicitly scoped type-theoretic formulations, not a literal ZFSet encoding of all categories.',
  YonedaAdjunction:'Primary 2.3, the non-assigned part of 2.6, 2.7, 3.1 and 3.4–3.7: definitions, non-exercise consequences and equivalence criterion. Assigned Yoneda/adjunction correspondence proofs are withheld.',
  TerminalCategory:'Primary 1.25, 1.27, 3.8 and 3.9: terminal category and finite example. The strict evaluation isomorphism assigned in 1.26 is withheld.',
  PathAndIdentity:'Introduction: endpoint-fixed path homotopies, their ordinary fundamental groupoid, and group invariants. This does not construct the full infinity-groupoid or prove univalence.',
  SourceLaws:'Ordinary-category supporting results. Exact source coverage is determined by source-audit.json, not by the module label.',
  SetFunctions:'Proved correspondence between functions of ZFC membership types and set-coded function graphs.',
  SetCategories:'Source category, functor, contravariant functor and natural-transformation definitions with literal set-universe membership; proved data-preserving Mathlib correspondences.',
  SetUniverseClosure:'Products and function sets derived from exactly the four stated set-universe assumptions.',
  SmallSetsCategory:'Example 1.8 and 1.10, Set case only: all small ZFC sets, actual function sets, local smallness, non-smallness and bijective isomorphisms.',
  SetCategoryEquivalences:'Exact set-coded formulations of 3.1 and 3.4–3.7, including both equivalences of an adjoint equivalence and the adjoint upgrade.',
  FiniteSetCategories:'Exact finite set-coded terminal category, walking isomorphism, object-selection uniqueness and inclusion equivalence.',
  SetCategoryModels:'General operation-preserving correspondence between specified ZFC object/hom codes and modeled categories; explicit fully faithful functor restrictions.',
  SetOption:'Disjoint addition of a distinguished point, with explicit Option equivalence and source-universe bound.',
  SmallPointedSets:'Actual pointed small-set category, exact morphism graphs, size bounds, non-smallness, isomorphism test and forgetful functor.',
  SmallPointedAdjunction:'The add-basepoint functor and unit/counit adjunction on the actual small-set categories, with proved commuting model squares.',
  SetSubsets:'Bijective correspondence between subsets of membership types and actual ZFC subsets.',
  SmallTopologicalSpaces:'All small topological spaces encoded by their carrier and open-set family; continuous graph morphisms, size bounds and homeomorphism test.',
  SmallTopologicalAdjunctions:'Exact discrete, forgetful and indiscrete functors; stated open-set families and both source adjunctions.',
  SmallVectorSpaces:'All vector-space structures on small ZFC sets, injective operation codes, linear graphs and the bijective isomorphism criterion.',
  SetFreeVectors:'Actual finitely supported coefficient graphs, their source-universe bounds and proved linear correspondence to the direct sum.',
  SmallVectorAdjunction:'Free and forgetful vector functors, their exact adjunction and non-smallness of the vector-space object collection.',
  SetRepresentableIsomorphism:'Non-exercise Corollary 2.7 with actual small-set-valued representables and componentwise natural isomorphisms; library prerequisites reused internally.',
  SetIndexedFamilies:'ZFC graphs of indexed set families, injectivity and closure under the source universe assumptions.',
  SetCategoryCodes:'Injective complete category codes with actual universe bounds and data-preserving restriction/enlargement.',
  SetFunctorCodes:'Injective exact functor codes in an explicit small bounding set.',
  SmallCategoryUniverse:'Remark 1.16: all source-small categories, small functor hom sets, non-small object collection, and exact huge-category inclusion.',
  ConcreteGroupPresentations:'Introduction: actual integer carriers {0,1} and {1,-1}, addition modulo two versus multiplication, isomorphism and unequal numerical identities.',
  SetCategoryPresentation:'Introduction to equivalences: strict inverse functors require an object bijection; the exact singleton and walking-isomorphism categories are not strictly isomorphic.'
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
  if(n.module==='ILab.MathematicsLearning.YonedaConstruction') n.verification='Verified author-supplied construction step only. The complete Yoneda theorem is not verified here. Candidate naturality, mutual inverseness, and naturality in c and F remain assigned exercises.';
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
