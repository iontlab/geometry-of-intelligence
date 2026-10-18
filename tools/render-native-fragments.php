<?php
// Use the existing local DokuWiki parser; never connect to a remote service.
$root=dirname(__DIR__);
$stage=dirname($root).'/mathematics-learning-20261018/native-publication';
define('DOKU_INC',dirname($root).'/explanation-layers-staging-20260921/tests/explanation-layers/runtime/');
define('DOKU_DISABLE_GZIP_OUTPUT',true);
require_once DOKU_INC.'inc/init.php';
require_once DOKU_INC.'inc/parserutils.php';
$conf['cachedir']=$stage.'/rendered/cache';
$conf['tocminheads']=0;
$input=json_decode(file_get_contents($stage.'/render-input.json'),true,512,JSON_THROW_ON_ERROR);
$out=['source_pdf_sha256'=>'5d773c2492817fbc366d7fe31fbac096dadadf2c3d24f616684a50b089f144bc','items'=>[]];
foreach($input as $item){
    $ID='mathematics_learning:higher_category_theory:synthetic_category_theory:'.$item['chapter'];
    $info=[];
    $markup=p_render('xhtml',p_get_instructions($item['render_source']),$info);
    $markup=preg_replace('/<!--.*?-->/s','',$markup);
    foreach($item['diagrams'] as $i=>$svg){
        $markup=str_replace('ILABNATIVEDIAGRAM'.$i.'TOKEN',$svg,$markup);
    }
    $out['items'][$item['key']]=['chapter'=>$item['chapter'],'source_sha256'=>$item['sha256'],'html'=>$markup];
}
$dest=$root.'/docs/formalization/mathematics-learning/explanations/native-source.json';
file_put_contents($dest,json_encode($out,JSON_UNESCAPED_UNICODE|JSON_UNESCAPED_SLASHES|JSON_THROW_ON_ERROR)."\n");
echo count($out['items'])." exact source fragments rendered.\n";
