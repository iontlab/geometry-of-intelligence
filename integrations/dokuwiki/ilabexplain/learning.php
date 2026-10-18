<?php
/** GPL-2.0-or-later. Learning extension of the existing source-bound explanation plugin. */
if (!defined('DOKU_INC')) die();
final class ILabLearningExplanation {
    private const BASE='formalization/mathematics-learning/explanations/';
    private static function json($name) {
        $path=DOKU_INC.self::BASE.$name;
        if (!is_file($path)||!is_readable($path)||filesize($path)>500000) throw new \RuntimeException('Unavailable');
        return json_decode(file_get_contents($path),true,32,JSON_THROW_ON_ERROR);
    }
    public static function matches($source,$fragment,$binding,$role) {
        return is_array($source)&&is_string($fragment)&&is_array($binding)
            &&($source['revision']??null)===($binding['revision']??null)
            &&($source['raw_sha256']??null)===($binding['raw_sha256']??null)
            &&in_array(hash('sha256',$fragment),$binding['fragments'][$role]??[],true);
    }
    public static function status() {
        $id=$_GET['id']??null;$nonce=$_GET['nonce']??null;
        if (($_SERVER['REQUEST_METHOD']??'')!=='GET'||!is_string($id)||!preg_match('/^mathematics_learning:higher_category_theory:synthetic_category_theory:(foundations|size|categories|functors|natural_transformations|yoneda|adjunctions|equivalences)$/D',$id)||!is_string($nonce)||!preg_match('/^[a-f0-9]{32}$/D',$nonce)||auth_quickaclcheck($id)<AUTH_READ) return ['available'=>false];
        $release=self::json('release.json');$contract=self::json('binding.json');$binding=$contract['pages'][$id]??null;
        $file=wikiFN($id);
        $source=action_plugin_ilabexplain::snapshot(function()use($file){clearstatcache(true,$file);return @filemtime($file);},fn()=>@file_get_contents($file));
        $registry=DOKU_INC.self::BASE.'registry.v0.1.json';
        $ok=($release['enabled']??false)===true&&($release['publication_authorized']??false)===true&&is_array($binding)&&is_array($source)&&$source['revision']===$binding['revision']&&$source['raw_sha256']===$binding['raw_sha256']&&is_file($registry)&&filesize($registry)<=500000&&hash_file('sha256',$registry)===($release['registry_sha256']??null);
        return ['available'=>$ok,'nonce'=>$nonce,'page_id'=>$id,'revision'=>$source['revision']??null,'raw_sha256'=>$source['raw_sha256']??null,'release'=>$release['release']??null,'registry_sha256'=>$release['registry_sha256']??null];
    }
    public static function display($event) {
        global $ID,$ACT,$REV,$INFO;
        if (($_SERVER['REQUEST_METHOD']??'')!=='GET'||$ACT!=='show'||!empty($REV)||auth_quickaclcheck($ID)<AUTH_READ) return;
        if (!preg_match('/^mathematics_learning:higher_category_theory:synthetic_category_theory:(foundations|size|categories|functors|natural_transformations|yoneda|adjunctions|equivalences)$/D',$ID)) return;
        // Editor-only binding capture returns digests, never source text or credentials.
        // It is an inert diagnostic on these eight pages, not an explanation release.
        if (($_GET['ilab_learning_capture']??null)==='1'&&!empty($_SERVER['REMOTE_USER'])&&($INFO['perm']??0)>=AUTH_EDIT) {
            $file=wikiFN($ID);
            $source=action_plugin_ilabexplain::snapshot(function()use($file){clearstatcache(true,$file);return @filemtime($file);},fn()=>@file_get_contents($file));
            if (!is_array($source)) return;
            $capture=['page_id'=>$ID]+$source+['role'=>'editor','fragment_sha256'=>hash('sha256',$event->data)];
            $event->data.='<script type="application/json" id="ilab-learning-capture">'.json_encode($capture,JSON_HEX_TAG|JSON_HEX_AMP|JSON_HEX_APOS|JSON_HEX_QUOT|JSON_THROW_ON_ERROR).'</script>';
            return;
        }
        $release=self::json('release.json');$contract=self::json('binding.json');
        if (($release['enabled']??false)!==true||($release['publication_authorized']??false)!==true||($release['render_contract']??null)!==($contract['render_contract']??null)) return;
        $path=DOKU_INC.self::BASE.'registry.v0.1.json';
        if (!is_file($path)||filesize($path)>500000) return;
        $bytes=file_get_contents($path);
        if (!is_string($bytes)||hash('sha256',$bytes)!==($release['registry_sha256']??null)) return;
        $reg=json_decode($bytes,true,32,JSON_THROW_ON_ERROR);
        if (($reg['release']['enabled']??false)!==true||($reg['release']['publication_authorized']??false)!==true) return;
        $records=array_values(array_filter($reg['records']??[],fn($r)=>($r['source']['page_id']??null)===$ID&&($r['wiki']??false)===true));
        if (!$records) return;
        $file=wikiFN($ID);
        $source=action_plugin_ilabexplain::snapshot(function()use($file){clearstatcache(true,$file);return @filemtime($file);},fn()=>@file_get_contents($file));
        $role=empty($_SERVER['REMOTE_USER'])?'anonymous':(($INFO['perm']??0)>=AUTH_EDIT?'editor':'reader');
        $binding=$contract['pages'][$ID]??null;
        if (!self::matches($source,$event->data,$binding,$role)) return;
        foreach($records as $r) {
            $s=$r['source'];
            if (($r['release_ready']??false)!==true||($r['review']['status']??null)!=='AI-authored; independent human review not claimed'||$s['revision']!==$source['revision']||$s['whole_page_sha256']!==$source['raw_sha256']) return;
            $heading=$s['heading_html_by_role'][$role]??($s['heading_html']??null);
            if (!is_string($heading)||substr_count($event->data,$heading)!==1||substr_count($event->data,'id="'.$s['anchor'].'"')!==1) return;
        }
        $token=['page_id'=>$ID]+$source+['fragment_sha256'=>hash('sha256',$event->data),'role'=>$role,'registry_sha256'=>$release['registry_sha256'],'release'=>$release['release'],'render_contract'=>$release['render_contract'],'keys'=>array_column($records,'object_key')];
        $base='/'.self::BASE;
        $version='?v='.rawurlencode($release['release']);
        $event->data.='<script type="application/json" id="ilab-learning-binding">'.json_encode($token,JSON_HEX_TAG|JSON_HEX_AMP|JSON_HEX_APOS|JSON_HEX_QUOT|JSON_THROW_ON_ERROR).'</script>'
            .'<link rel="stylesheet" href="'.$base.'explanations.css'.$version.'"><script src="'.$base.'renderer.js'.$version.'"></script><script src="'.$base.'statement-adapter.js'.$version.'"></script><script src="'.$base.'wiki-adapter.js'.$version.'" defer></script>';
    }
}
