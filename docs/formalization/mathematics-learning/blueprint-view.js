'use strict';
const modeElement = id => document.getElementById(id);
// Visibility comes only from existing authored mappings. No edges are defined here.
let graphMode = new URLSearchParams(location.search).get('view') === 'lean' ? 'lean' : 'blueprint';
let blueprintIds = new Set();
const blueprintGroups = {
  'ILab.MathematicsLearning.BasicCategoryTheory': 'Identity laws and inverse uniqueness',
  'ILab.MathematicsLearning.WalkingIsomorphism': 'A finite walking isomorphism',
  'ILab.MathematicsLearning.SetUniverses': 'Set universes and equality transport',
  'ILab.MathematicsLearning.CategoryConstructions': 'Categories, functors and adjunction examples',
  'ILab.MathematicsLearning.CategorySize': 'Size and local smallness',
  'ILab.MathematicsLearning.YonedaAdjunction': 'Non-exercise Yoneda consequences and equivalences',
  'ILab.MathematicsLearning.TerminalCategory': 'Terminal category and finite object counts',
  'ILab.MathematicsLearning.PathAndIdentity': 'Paths up to homotopy and group invariance',
  'ILab.MathematicsLearning.SourceLaws': 'Definitions and their supplied laws'
};
function updateGraphModeControls() {
  modeElement('mode-blueprint').setAttribute('aria-pressed', String(graphMode === 'blueprint'));
  modeElement('mode-lean').setAttribute('aria-pressed', String(graphMode === 'lean'));
  modeElement('generated-control').hidden = graphMode === 'blueprint';
  modeElement('generated').disabled = graphMode === 'blueprint';
  modeElement('mode-description').textContent = graphMode === 'blueprint'
    ? 'Curated view of the verified mathematical results and their formal dependencies.'
    : 'Complete project-local Lean declaration graph, including implementation and helper declarations.';
}
function setGraphMode(mode) {
  if (graphMode === mode) return;
  graphMode = mode;
  modeElement('module').value = 'all'; modeElement('search').value = ''; modeElement('generated').checked = false;
  selected = null; scale = 1;
  updateGraphModeControls();
  const url = new URL(location.href);
  if (mode === 'lean') url.searchParams.set('view', 'lean'); else url.searchParams.delete('view');
  history.replaceState(null, '', url);
  render(); modeElement('viewport').scrollTo(0, 0);
}
async function initializeGraphModes() {
  const metadata = await authoredMathematics;
  if (metadata) blueprintIds = new Set(Object.keys(metadata.declarations));
  else {
    graphMode = 'lean';
    modeElement('mode-blueprint').disabled = true;
    modeElement('mode-blueprint').title = 'Authored mathematics metadata could not load.';
  }
  updateGraphModeControls();
}
modeElement('mode-blueprint').onclick = () => setGraphMode('blueprint');
modeElement('mode-lean').onclick = () => setGraphMode('lean');
updateGraphModeControls();
