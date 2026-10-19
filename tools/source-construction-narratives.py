"""Only the six newly authorized graph narratives; published narratives are immutable."""
NARRATIVES={
'1.15':('Categories as objects',
 'A category of categories uses categories as objects and functors as arrows. Identity leaves objects and arrows unchanged; composition applies F, then G. Existing set codes represent these data. The formulas do not supply the assigned category-law proof.',
 ['Mira catalogues entire towns, each with its own places and routes. A translation between towns carries both places and routes; two translations are followed in order.', 'Her identity translation changes nothing. Writing these recipes does not certify that every way of composing translations agrees: that audit is still the students’ task.'],
 'Towns and translations','Set-coded categories and functors'),
'1.17':('Reversing raw arrows',
 'The opposite keeps the same objects, uses C(y,x) for arrows x→y, and keeps identity arrows. Its composite uses the original composition in reverse order. Lean checks these typed data and equations, not the assigned proof that they form a category.',
 ['Mira redraws the town map with every arrow reversed, keeping all places. A route formerly running z→y→x is read as x→y→z on the new sheet.', 'The new composite therefore comes from the old route in reversed order. The drawing supplies a recipe; the students must still check its category laws.'],
 'Reversed map','Opposite object, hom and composition data'),
'1.21':('Appending a fixed arrow',
 'Fix f:c→d. At any x, the supplied component sends g:x→c to the composite g ≫ f:x→d. This is a function between the source hom sets. Compatibility as x varies is naturality, and remains an exercise.',
 ['Fern appends the same final road c→d to every route arriving at c. A traveller starting at x now receives a route from x to d.', 'This works as a local routing recipe. Whether rerouting the approach commutes with the recipe everywhere is a separate consistency check, still assigned to the students.'],
 'Appending the final road','Postcomposition component g↦g ≫ f'),
'1.23':('Identity and vertical components',
 'For a given functor F, the identity component at x is id at F(x). Given α:F⇒G and β:G⇒K, the composite component is α_x followed by β_x. These are raw arrows; transformation naturality and the functor-category laws remain assigned.',
 ['Three translators give three versions of each town document. Mira passes one version through α and then β; at that document, the two passes form one composite.', 'Doing nothing gives the identity pass. A recipe at each document does not yet certify compatibility with every document link, or all category laws.'],
 'Passes between document versions','Transformation components and their vertical composite'),
'1.28':('Two ways to compose',
 'Precomposition sends G to G after F and reads a transformation at F(x). Postcomposition sends G to F after G and applies F to its component at x. Both reuse existing functor composition. The two whole-functor well-definedness checks remain exercises.',
 ['Fern can change which document a translator receives, or translate the response after it arrives. In the first case she reads the existing comparison at the changed input; in the second she translates the comparison itself.', 'These are different operations with different starting and ending points. The recipes alone do not certify all required compatibility checks.'],
 'Changed input versus translated response','Precomposition α_(Fx) versus postcomposition F(α_x)'),
'3.3':('Four adjunction formulas',
 'A given adjunction supplies g↦η_x ≫ R(g) and f↦L(f) ≫ ε_y. Conversely, given hom-set bijections φ natural in both variables, applying φ to id at Lx gives a unit candidate; applying inverse φ to id at Ry gives a counit candidate. Only these formulas are checked; inverses, naturality and triangles remain assigned.',
 ['Mira has two offices for describing delivery requests. The existing charter gives two translation recipes. With a given consistent matching of request catalogues instead, she translates the do-nothing requests to obtain candidate comparison slips.', 'Writing those slips does not certify that the reconstructed charter works. The students must still check consistency and the round-trip rules.'],
 'Translation recipes and comparison slips','Hom functions and unit/counit candidates'),
}
def content(key):
    title,plain,story,element,counterpart=NARRATIVES[key]
    paragraph=lambda s:{'type':'paragraph','text':s}
    return {'plain':{'title':title,'blocks':[paragraph(plain)]},
      'story':{'title':'Story / Fairy Tale · '+key,'label':'Story analogy','disclaimer':'This story is an analogy, not the mathematical statement or proof.','blocks':[paragraph(s) for s in story]},
      'story_key':[{'story_element':element,'scientific_counterpart':counterpart}],
      'where_analogy_stops':[paragraph('The analogy describes only the supplied data. It proves no category/functor laws, naturality, inverse or triangle checks; the assigned exercises remain open.')]}
