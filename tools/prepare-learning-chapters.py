"""Prepare numbered anchors inside the approved eight existing lessons.

No network write is performed. Review and publish through the authenticated
DokuWiki editor, then capture the actual rendered anchors for release binding.
"""
from pathlib import Path
import argparse,json,re

parser=argparse.ArgumentParser()
parser.add_argument('--source-dir',type=Path,required=True)
parser.add_argument('--output-dir',type=Path,required=True)
args=parser.parse_args();args.output_dir.mkdir(parents=True,exist_ok=True)
ROOT=Path(__file__).resolve().parents[1]
inventory=json.loads((ROOT/'docs/mathematics-learning/obligations.json').read_text('utf-8'))['records']
lessons=['foundations','size','categories','functors','natural_transformations','yoneda','adjunctions','equivalences']
sources={l:(args.source_dir/(l+'.txt')).read_text('utf-8') for l in lessons}

def replace(lesson,old,new):
    assert sources[lesson].count(old)==1,(lesson,old)
    sources[lesson]=sources[lesson].replace(old,new)

replace('categories','**Definition 1.5 and Remark 1.6.**','**Definition 1.5.**')
replace('categories','A huge strict category uses huge object and hom sets instead. Merely drawing arrows does not specify a category: the composites and laws must also be given.', 'Merely drawing arrows does not specify a category: the composites and laws must also be given.\n\n**Remark 1.6.** By convention the object set and hom sets are large. A huge strict category uses huge object and hom sets instead.')
s=sources['categories'];a=s.index('**Examples 1.8 and 1.10.**');b=s.index('**Definition 1.9.**',a)
old_table=s[a:b]
new_table=r'''**Example 1.8.**

^ Category ^ Objects and morphisms ^
| \(\mathbf{Set}\) | Small sets and functions |
| \(\mathbf{Set}_*\) | Small pointed sets and basepoint-preserving functions |
| \(\mathbf{Vect}_k\) | Small vector spaces over a fixed small field \(k\), with linear maps |
| \(\mathbf{Top}\) | Small topological spaces and continuous maps |

Identity maps and ordinary function composition preserve each specified structure. Hom sets are subsets of function sets, which accounts for local smallness in the universe setting. These categories are not small under the source's convention.

'''
s=s[:a]+new_table+s[b:]
iso_table=r'''**Example 1.10.**

^ Category ^ Isomorphisms ^
| \(\mathbf{Set}\) | Bijections |
| \(\mathbf{Set}_*\) | Basepoint-preserving bijections |
| \(\mathbf{Vect}_k\) | Linear bijections |
| \(\mathbf{Top}\) | Homeomorphisms |

For pointed sets, the inverse of a pointed bijection is pointed; for vector spaces, a bijective linear map has a linear inverse. Continuity of an inverse needs its own hypothesis, as the two-point example shows.

'''
s=s.replace('**Proposition 1.11, independent proof.**',iso_table+'**Proposition 1.11, independent proof.**')
sources['categories']=s
replace('functors','**Construction 1.15 and Remark 1.16.**','**Construction 1.15.**')
replace('functors',"In the primary's hierarchy,", "**Remark 1.16.** In the primary's hierarchy,")
replace('yoneda','Assume \\(C\\) is locally small, and write \\(h_c=C(-,c)\\). A presheaf here means a functor \\(F:C^{op}\\to\\mathbf{Set}\\). **Theorem 2.1** gives','**Theorem 2.1.** Assume \\(C\\) is locally small, and write \\(h_c=C(-,c)\\). A presheaf here means a functor \\(F:C^{op}\\to\\mathbf{Set}\\). The theorem gives')

# The introductory source's actual structural/nonstructural group example.
replace('foundations','For an independent example,',r'''The primary compares the isomorphic groups \((\{0,1\},+\bmod 2)\) and \((\{1,-1\},\cdot)\). Having an element of order two is invariant under group isomorphism. Having the particular number \(0\) as identity depends on the chosen presentation: it holds for the first group but not the second.

For an independent example,''')

anchors={}
for r in inventory:
    if r['kind']=='unnumbered':continue
    key=r['key'];lesson=r['lesson'];title=r['kind']+' '+key
    # Existing labels include optional editorial subtitles after comma or colon.
    pattern=r'\*\*'+re.escape(title)+r'(?:[.,:]|\*\*)[^\n]*?\*\*\s*'
    matches=list(re.finditer(pattern,sources[lesson]))
    assert len(matches)==1,(key,len(matches))
    m=matches[0];sources[lesson]=sources[lesson][:m.start()]+'==== '+title+' ====\n\n'+sources[lesson][m.end():]
    anchors[key]={'lesson':lesson,'heading_text':title,'inline':True}

intro_titles=['Informal higher-dimensional picture','Topological motivation','Identity types and transport','Structure Identity Principle','Synthetic foundations','Boundary of this lesson']
for title in intro_titles:
    replace('foundations','**'+title+'.**','==== '+title+' ====\n\n')
intro_bindings={
'intro.what':'Informal higher-dimensional picture','intro.higher_morphisms':'Informal higher-dimensional picture','intro.invertibility':'Informal higher-dimensional picture',
'intro.paths':'Topological motivation','intro.groupoids':'Topological motivation','intro.models':'Plain Language',
'intro.hott':'Identity types and transport','intro.identity':'Identity types and transport','intro.sip':'Structure Identity Principle',
'intro.synthetic':'Synthetic foundations','intro.course':'Plain Language','strict.motivation':'Boundary of this lesson',
'equivalences.motivation':'Plain Language','3.5.adjoint_upgrade':'Example 3.5'}
for r in inventory:
    if r['kind']=='unnumbered':anchors[r['key']]={'lesson':r['lesson'],'heading_text':intro_bindings[r['key']],'inline':r['key'] in {'intro.paths','intro.sip','3.5.adjoint_upgrade'}}

for lesson,s in sources.items():
    # Keep the existing five chapter sections; item controls carry exact scopes.
    s=s.replace('**Not formalized**','**Formalization status is item-specific; see Lean and Verification**')
    a=s.index('===== Lean =====');b=s.index('Next:',a) if 'Next:' in s[a:] else s.index('Return:',a)
    checked=[r for r in inventory if r['lesson']==lesson and r['lean_declarations']]
    assigned=[r['key'] for r in inventory if r['lesson']==lesson and r.get('exercise_exclusion')]
    text='===== Lean =====\n\nThe statement controls show the exact checked Lean signatures, source modules and pinned source links for the mapped non-exercise material. ' if checked else '===== Lean =====\n\nFormalization status is attached to the individual source items. '
    if lesson in ['foundations','size','categories','functors']:
        text+='Lean type universes are distinguished from the source’s explicit set-universe assumptions. Higher identity types, univalence and full synthetic foundations are not asserted as Lean theorems. '
    if assigned:text+='Assigned solutions are withheld for '+', '.join(assigned)+'. '
    text+='\n\n===== Verification =====\n\nThe controls distinguish checked definitions, exact Mathlib reuse, new Lean proofs, foundation limitations and intentionally withheld exercise solutions. Each mapping states its scope and actual compiler-derived dependencies; none is a claim that every mathematical statement in this chapter is fully formalized. [[:mathematics_learning:higher_category_theory:synthetic_category_theory:verification|Complete verification record]] · [[:mathematics_learning:higher_category_theory:synthetic_category_theory:coverage|Source inventory and exercise exclusions]].\n\n'
    s=s[:a]+text+s[b:]
    (args.output_dir/(lesson+'.txt')).write_text(s,encoding='utf-8',newline='\n')
    expected=[r['kind']+' '+r['key'] for r in inventory if r['lesson']==lesson and r['kind']!='unnumbered']
    actual=re.findall(r'^==== ((?:Definition|Remark|Convention|Example|Proposition|Construction|Theorem|Corollary) \d+\.\d+) ====$',s,re.M)
    assert actual==expected,(lesson,actual,expected)
(args.output_dir/'statement-headings.json').write_text(json.dumps(anchors,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
print('Prepared all 44 numbered anchors in source order, plus scoped introductory controls, inside the existing eight lessons.')
