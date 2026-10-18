<?php
$repo=dirname(__DIR__).'/';
$fixture=sys_get_temp_dir().'/ilab-learning-fixture-'.bin2hex(random_bytes(8)).'/';@mkdir($fixture.'formalization/mathematics-learning/explanations/',0777,true);
define('DOKU_INC',$fixture);define('AUTH_READ',1);define('AUTH_EDIT',2);
class DokuWiki_Action_Plugin {}
require $repo.'integrations/dokuwiki/ilabexplain/action.php';
require $repo.'integrations/dokuwiki/ilabexplain/learning.php';
$acl=2;function auth_quickaclcheck($id){global $acl;return $acl;}
function wikiFN($id){return DOKU_INC.'source.txt';}
$raw="Independent fixture: inverse uniqueness.\n";$revision=1792304639;
file_put_contents(wikiFN(''),$raw);touch(wikiFN(''),$revision);
$fragment='<h4 id="mw_1_11">Proposition 1.11</h4><p>Two inverses agree.</p>';
$id='mathematics_learning:higher_category_theory:synthetic_category_theory:categories';
$source=['revision'=>$revision,'raw_sha256'=>hash('sha256',$raw)];
$binding=$source+['fragments'=>['anonymous'=>[hash('sha256',$fragment)]]];
$records=[['object_key'=>'explain.mathematics-learning.1.11','wiki'=>true,'source'=>['page_id'=>$id,'revision'=>$revision,'whole_page_sha256'=>$source['raw_sha256'],'anchor'=>'mw_1_11','heading_html'=>'<h4 id="mw_1_11">Proposition 1.11</h4>'],'release_ready'=>true,'review'=>['status'=>'AI-authored; independent human review not claimed']]];
$base=DOKU_INC.'formalization/mathematics-learning/explanations/';
$reg=['records'=>$records,'release'=>['enabled'=>true,'publication_authorized'=>true]];
$bytes=json_encode($reg);file_put_contents($base.'registry.v0.1.json',$bytes);
$release=['enabled'=>true,'publication_authorized'=>true,'release'=>'fixture-1','registry_sha256'=>hash('sha256',$bytes),'render_contract'=>'fixture-exact-1'];
file_put_contents($base.'release.json',json_encode($release));
$contract=['render_contract'=>'fixture-exact-1','pages'=>[$id=>$binding]];
file_put_contents($base.'binding.json',json_encode($contract));
$results=[];function check($name,$ok){global $results;$results[]=['test'=>$name,'pass'=>(bool)$ok];if(!$ok)throw new Exception($name);}
$ID=$id;$ACT='show';$REV=0;$INFO=['perm'=>1];$_SERVER=['REQUEST_METHOD'=>'GET'];
$plugin=new action_plugin_ilabexplain();
function display($fragment){global $plugin;$e=(object)['data'=>$fragment];$plugin->displayLearning($e,null);return $e->data;}
check('exact current source and fragment receive learning assets',str_contains(display($fragment),'ilab-learning-binding'));
check('original fragment is preserved as an exact prefix',str_starts_with(display($fragment),$fragment));
check('modified fragment is withheld',display($fragment.' ')===$fragment.' ');
check('renamed anchor is withheld',display(str_replace('mw_1_11','changed',$fragment))===str_replace('mw_1_11','changed',$fragment));
check('duplicate anchor is withheld',display($fragment.$fragment)===$fragment.$fragment);
check('unknown role is withheld',!ILabLearningExplanation::matches($source,$fragment,$binding,'reader'));
check('changed source hash is withheld',!ILabLearningExplanation::matches(['revision'=>$revision,'raw_sha256'=>str_repeat('0',64)],$fragment,$binding,'anonymous'));
check('same bytes with new revision are withheld',!ILabLearningExplanation::matches(['revision'=>$revision+1,'raw_sha256'=>$source['raw_sha256']],$fragment,$binding,'anonymous'));
foreach(['edit','preview','revisions','diff','export_raw','export_xhtml'] as $act){$ACT=$act;check('withhold '.$act,display($fragment)===$fragment);}$ACT='show';
$REV=$revision;check('historical show is withheld',display($fragment)===$fragment);$REV=0;
$acl=0;check('ACL denial is preserved',display($fragment)===$fragment);$acl=2;
$ID='research:rq001_phase_i';check('RQ-001 never enters learning handler',display($fragment)===$fragment);$ID=$id;
$_SERVER['REQUEST_METHOD']='POST';check('POST is withheld',display($fragment)===$fragment);$_SERVER['REQUEST_METHOD']='GET';
$_GET=['id'=>$id,'nonce'=>str_repeat('a',32)];$s=ILabLearningExplanation::status();check('freshness endpoint returns exact revision and digest',$s['available']&&$s['revision']===$revision&&$s['raw_sha256']===$source['raw_sha256']);
$_GET['id']='private:other';check('endpoint rejects unrelated IDs',ILabLearningExplanation::status()===['available'=>false]);$_GET['id']=$id;
$_GET['nonce']='bad';check('endpoint rejects malformed nonce',ILabLearningExplanation::status()===['available'=>false]);$_GET['nonce']=str_repeat('a',32);
$acl=0;check('endpoint respects ACL',ILabLearningExplanation::status()===['available'=>false]);$acl=2;
$release['enabled']=false;file_put_contents($base.'release.json',json_encode($release));check('release off withholds UI',display($fragment)===$fragment);check('release off disables freshness',ILabLearningExplanation::status()['available']===false);
$release['enabled']=true;file_put_contents($base.'release.json',json_encode($release));file_put_contents($base.'registry.v0.1.json',$bytes.' ');check('registry hash mismatch withholds UI',display($fragment)===$fragment);check('registry hash mismatch disables freshness',ILabLearningExplanation::status()['available']===false);
file_put_contents($base.'registry.v0.1.json',$bytes);check('restored fixture works',str_contains(display($fragment),'ilab-learning-binding'));
$_GET['ilab_learning_capture']='1';
check('anonymous cannot request editor capture',!str_contains(display($fragment),'ilab-learning-capture'));
$_SERVER['REMOTE_USER']='fixture-editor';$INFO['perm']=AUTH_EDIT;
$captured=display($fragment);
check('editor digest capture preserves exact fragment prefix',str_starts_with($captured,$fragment));
check('editor capture contains exact server fragment digest',str_contains($captured,hash('sha256',$fragment)));
check('editor capture contains no source text or explanation loader',!str_contains($captured,$raw)&&!str_contains($captured,'renderer.js'));
$INFO['perm']=AUTH_READ;check('reader cannot request editor capture',!str_contains(display($fragment),'ilab-learning-capture'));
$ID='research:rq001_phase_i';$INFO['perm']=AUTH_EDIT;check('capture remains outside RQ-001',display($fragment)===$fragment);
if(isset($argv[1]))file_put_contents($argv[1],json_encode($results,JSON_PRETTY_PRINT));echo count($results)." source-binding and isolation checks passed\n";
