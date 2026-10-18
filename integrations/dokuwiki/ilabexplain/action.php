<?php
/** GPL-2.0-or-later. Exact-fragment contract, deliberately no normalization. */
if (!defined('DOKU_INC')) die();
class action_plugin_ilabexplain extends DokuWiki_Action_Plugin {
    public function register(Doku_Event_Handler $controller) {
        $controller->register_hook('TPL_CONTENT_DISPLAY','BEFORE',$this,'display');
        $controller->register_hook('TPL_CONTENT_DISPLAY','BEFORE',$this,'displayLearning');
        $controller->register_hook('AJAX_CALL_UNKNOWN','BEFORE',$this,'statusLearning');
        $controller->register_hook('AJAX_CALL_UNKNOWN','BEFORE',$this,'status');
    }
    private function files() {
        return defined('ILAB_EXPLAIN_ASSETS') ? ILAB_EXPLAIN_ASSETS : DOKU_INC.'explanations/rq001/';
    }
    private function bytes($name) {
        $private=in_array($name,['binding.json','registry.v0.1.json'],true) && $this->privatePreview();
        $file=($private?$this->privateFiles():$this->files()).$name;
        if (!is_file($file) || !is_readable($file) || filesize($file)>500000) return null;
        $bytes=file_get_contents($file);
        return is_string($bytes) && strlen($bytes)<=500000 ? $bytes : null;
    }
    private function privateFiles() {
        // Hetzner's public_html is a web-root alias, not the physical sibling of its home.
        return is_dir('/usr/home/iontla/ilab-explain-private')?'/usr/home/iontla/ilab-explain-private/':dirname(rtrim(DOKU_INC,'/\\')).'/ilab-explain-private/';
    }
    private function json($name) { $bytes=$this->bytes($name);return $bytes===null?null:json_decode($bytes,true,32,JSON_THROW_ON_ERROR); }
    private static function digest($v) {return is_string($v) && preg_match('/^[a-f0-9]{64}$/D',$v)===1;}
    private static function text($v,$max=12000) {return is_string($v) && strlen($v)>0 && strlen($v)<=$max;}
    private static function flags($v) {return is_array($v) && isset($v['enabled'],$v['publication_authorized']) && is_bool($v['enabled']) && is_bool($v['publication_authorized']);}
    private static function contract($c) {
        if (!is_array($c) || ($c['page_id']??null)!=='research:rq001_phase_i' || !is_int($c['revision']??null) || $c['revision']<=0 || !self::digest($c['raw_sha256']??null) || ($c['render_contract']??null)!=='mort-exact-fragment-1' || !is_array($c['fragments']??null) || empty($c['fragments']['anonymous'])) return false;
        foreach($c['fragments'] as $role=>$hashes) {
            if (!in_array($role,['anonymous','reader','editor'],true) || !is_array($hashes) || !array_is_list($hashes) || count($hashes)>8) return false;
            foreach($hashes as $hash) if(!self::digest($hash)) return false;
        }
        return true;
    }
    private static function records($records) {
        if(!is_array($records) || !array_is_list($records) || count($records)!==7)return false;
        $keys=[];$declarations=[];
        foreach($records as $r) {
            if(!is_array($r) || !self::text($r['object_key']??null,100) || !preg_match('/^explain\.rq001\.phase1\.(overview|capability-order|capability-monotonicity|update-probe-refinement|failure-of-descent|transformation-quotient|symmetry-obstruction)$/D',$r['object_key']) || in_array($r['object_key'],$keys,true) || !is_bool($r['release_ready']??null) || ($r['locale']??null)!=='en' || !is_array($r['source']??null) || !is_array($r['formal_mapping']??null) || !is_array($r['review']??null)) return false;
            $keys[]=$r['object_key'];$s=$r['source'];$f=$r['formal_mapping'];
            if(($s['page_id']??null)!=='research:rq001_phase_i' || !is_int($s['revision']??null) || !self::digest($s['whole_page_sha256']??null) || !self::text($s['anchor']??null,200) || !preg_match('/^[a-z0-9_-]+$/D',$s['anchor']) || !self::text($s['heading_html']??null,1500) || !self::text($s['heading_text']??null,1000) || !array_key_exists('declaration',$f))return false;
            foreach(['approved_by','approved_at'] as $key)if(!array_key_exists($key,$r['review']) || ($r['review'][$key]!==null && !self::text($r['review'][$key],200)))return false;
            if($f['declaration']!==null){if(!self::text($f['declaration'],200) || in_array($f['declaration'],$declarations,true) || !self::digest($f['source_sha256']??null) || !self::digest($f['mathematics_json_sha256']??null) || !is_string($f['source_commit']??null) || !preg_match('/^[a-f0-9]{40}$/D',$f['source_commit']))return false;$declarations[]=$f['declaration'];}
            elseif($r['object_key']!=='explain.rq001.phase1.overview')return false;
            $c=$r['content']??null;if(!is_array($c)||!is_array($c['plain']??null)||!is_array($c['story']??null)||!self::text($c['plain']['title']??null)||!self::text($c['story']['title']??null)||($c['story']['disclaimer']??null)!=='This story is an analogy, not the mathematical statement or proof.')return false;
            foreach([$c['plain']['blocks']??null,$c['story']['blocks']??null,$c['where_analogy_stops']??null] as $blocks){if(!is_array($blocks)||!array_is_list($blocks)||count($blocks)<1||count($blocks)>50)return false;foreach($blocks as $block)if(!is_array($block)||($block['type']??null)!=='paragraph'||!self::text($block['text']??null))return false;}
            if(!is_array($c['story_key']??null)||!array_is_list($c['story_key'])||count($c['story_key'])<1||count($c['story_key'])>30)return false;
            foreach($c['story_key'] as $row)if(!is_array($row)||!self::text($row['story_element']??null)||!self::text($row['scientific_counterpart']??null))return false;
        }
        return count($declarations)===6;
    }
    public function preview() {
        return defined('ILAB_EXPLAIN_LOCAL_PREVIEW') && ILAB_EXPLAIN_LOCAL_PREVIEW === true
            && in_array($_SERVER['REMOTE_ADDR'] ?? '',['127.0.0.1','::1'],true)
            && preg_match('/^(127\.0\.0\.1|localhost|\[::1\])(:[0-9]+)?$/D',$_SERVER['HTTP_HOST'] ?? '') === 1;
    }
    public function privatePreview() {
        if (($_SERVER['REQUEST_METHOD']??'')!=='GET' || ($_GET['ilab_explain_preview']??null)!=='1'
            || empty($_SERVER['REMOTE_USER']) || !auth_isadmin() || auth_quickaclcheck('research:rq001_phase_i')<AUTH_READ) return false;
        $path=$this->privateFiles().'permission.json';
        if(!is_file($path)||!is_readable($path)||filesize($path)>4096)return false;
        $p=json_decode(file_get_contents($path),true,8,JSON_THROW_ON_ERROR);
        $r=$this->json('release.json');
        return is_array($p)&&($p['admin_preview_enabled']??null)===true
            &&($p['release']??null)==='rq001-preview-0.1'&&($r['release']??null)===$p['release']
            &&($r['enabled']??null)===false&&($r['publication_authorized']??null)===false
            &&($r['registry_sha256']??null)==='84c10e4f080e4adbbcfe4051338254d819dc0cde27ff6b3b61dece21180ad9af';
    }
    private function state() {
        $release=$this->json('release.json'); $contract=$this->json('binding.json');
        $bytes=$this->bytes('registry.v0.1.json');
        $reg=$bytes===null?null:json_decode($bytes,true,32,JSON_THROW_ON_ERROR);
        if (!self::flags($release) || !self::text($release['release']??null,100) || !self::digest($release['registry_sha256']??null) || ($release['render_contract']??null)!=='mort-exact-fragment-1' || (array_key_exists('preview_disabled',$release) && !is_bool($release['preview_disabled'])) || !self::contract($contract) || !is_array($reg) || ($reg['schema_version']??null)!=='explanation-content-draft-1' || !self::flags($reg['release']??null) || !self::records($reg['records']??null) || !is_array($reg['content_format']??null) || ($reg['content_format']['version']??null)!=='plain-text-blocks-1'
            || !hash_equals($release['registry_sha256'],hash('sha256',$bytes))) return null;
        if(!is_array($reg['graph']??null)||!self::digest($reg['graph']['data_sha256']??null)||!self::digest($reg['graph']['mathematics_sha256']??null)||!is_array($reg['repository']??null)||!is_string($reg['repository']['commit']??null)||!preg_match('/^[a-f0-9]{40}$/D',$reg['repository']['commit']))return null;
        foreach($reg['records'] as $record)if($record['source']['revision']!==$contract['revision']||$record['source']['whole_page_sha256']!==$contract['raw_sha256'])return null;
        $production=($release['enabled']??false) === true && ($release['publication_authorized']??false) === true;
        if (!$this->preview() && !$this->privatePreview()) {
            if (!$production || !($reg['release']['enabled']??false) || !($reg['release']['publication_authorized']??false)) return null;
            foreach($reg['records'] as $r) if (!$r['release_ready'] || !$r['review']['approved_by'] || !$r['review']['approved_at']) return null;
        }
        if (($release['preview_disabled']??false) === true) return null;
        return [$release,$contract,$reg];
    }
    public function readSource() {
        $fn=wikiFN('research:rq001_phase_i');
        return self::snapshot(function()use($fn){clearstatcache(true,$fn);return @filemtime($fn);},function()use($fn){return @file_get_contents($fn);});
    }
    public static function snapshot($revision,$read) {
        $before=$revision(); $bytes=$read(); $after=$revision();
        // Second byte read also detects an edit retaining the filesystem timestamp.
        $again=$read();
        if (!$before || $before!==$after || $after!==$revision() || $bytes===false || $bytes!==$again) return null;
        return ['revision'=>$before,'raw_sha256'=>hash('sha256',$bytes)];
    }
    public static function valid($source,$fragment,$contract,$records,$role) {
        if (!is_array($source) || !is_string($fragment) || !self::contract($contract) || !self::records($records) || !is_string($role) || ($source['revision']??null)!==($contract['revision']??null)
            || ($source['raw_sha256']??null)!==($contract['raw_sha256']??null)
            || ($contract['render_contract']??'')!=='mort-exact-fragment-1'
            || !in_array(hash('sha256',$fragment),$contract['fragments'][$role]??[],true)) return false;
        foreach($records as $r) {
            if ($r['source']['revision']!==$source['revision'] || $r['source']['whole_page_sha256']!==$source['raw_sha256']) return false;
            if (substr_count($fragment,'id="'.$r['source']['anchor'].'"')!==1 || substr_count($fragment,$r['source']['heading_html'])!==1) return false;
            if ($r['formal_mapping']['declaration'] && !preg_match('/'.preg_quote($r['source']['heading_html'],'/').'\s*<div class="level3">/u',$fragment)) return false;
        }
        $edit=$role==='editor'?'(?:<div class="secedit editbutton_section editbutton_1">(?:(?!<h[1-6]\\b).)*?</form></div>\\s*)?':'';
        return preg_match('~</p>\s*</div>\s*'.$edit.'<h2[^>]*id="abstract"~su',$fragment) === 1;
    }
    public function display($event,$param) {
        // This boundary contains only this optional feature; unrelated DokuWiki errors are untouched.
        $original=$event->data;
        try { $this->displayChecked($event,$param); }
        catch (\Throwable $error) { $event->data=$original; }
    }
    private function displayChecked($event,$param) {
        global $ID,$ACT,$REV,$INFO;
        if (($_SERVER['REQUEST_METHOD']??'')!=='GET' || $ID!=='research:rq001_phase_i' || $ACT!=='show' || !empty($REV) || auth_quickaclcheck($ID)<AUTH_READ) return;
        $role=empty($_SERVER['REMOTE_USER'])?'anonymous':(($INFO['perm']??0)>=AUTH_EDIT?'editor':'reader');
        $fragment=$event->data;
        // Calibration is available only to this loopback fixture router, never a URL parameter.
        if ($this->preview() && defined('ILAB_EXPLAIN_CAPTURE')) file_put_contents(ILAB_EXPLAIN_CAPTURE,$fragment);
        $state=$this->state(); if (!$state) return;
        [$release,$contract,$reg]=$state; $source=$this->readSource();
        if (!self::valid($source,$fragment,$contract,$reg['records'],$role)) return;
        $token=['page_id'=>$ID]+$source+[
            'fragment_sha256'=>hash('sha256',$fragment),'render_contract'=>$contract['render_contract'],
            'release'=>$release['release'],'registry_sha256'=>$release['registry_sha256'],
            'local_preview'=>$this->preview(),'private_preview'=>$this->privatePreview(),'keys'=>array_column($reg['records'],'object_key')];
        if($this->privatePreview()){header('Cache-Control: no-store, private, max-age=0');header('Vary: Cookie');}
        $suffix='<script type="application/json" id="ilab-explain-binding">'.json_encode($token,JSON_HEX_TAG|JSON_HEX_AMP|JSON_HEX_APOS|JSON_HEX_QUOT|JSON_THROW_ON_ERROR).'</script>'
            .'<link rel="stylesheet" href="/explanations/rq001/explanations.css">'
            .'<script src="/explanations/rq001/renderer.js"></script><script src="/explanations/rq001/wiki-adapter.js" defer></script>';
        $event->data=$fragment.$suffix;
    }
    public function status($event,$param) {
        if (!in_array($event->data,['ilabexplain_status','ilabexplain_private'],true)) return;
        $event->preventDefault(); $event->stopPropagation();
        header('Content-Type: application/json'); header('Cache-Control: no-store, private, max-age=0');
        header('Vary: Cookie');header('X-Content-Type-Options: nosniff');
        if($event->data==='ilabexplain_private') {
            try {
                $ok=$this->privatePreview();$state=$ok?$this->state():null;$source=$state?$this->readSource():null;
                if(!$state||!$source||$source['revision']!==$state[1]['revision']||$source['raw_sha256']!==$state[1]['raw_sha256'])throw new \RuntimeException();
                echo json_encode(['private_preview'=>true,'registry'=>$this->bytes('registry.v0.1.json'),'release'=>$state[0],'contract'=>$state[1]],JSON_THROW_ON_ERROR);
            } catch (\Throwable $error) {http_response_code(403);echo '{"available":false}';}
            return;
        }
        $nonce=$_GET['nonce']??'';
        if (($_SERVER['REQUEST_METHOD']??'')!=='GET' || !is_string($nonce) || strlen($nonce)!==32 || !preg_match('/^[a-f0-9]{32}$/D',$nonce) || auth_quickaclcheck('research:rq001_phase_i')<AUTH_READ) {http_response_code(400);echo '{"available":false}';return;}
        try { $state=$this->state(); $source=$this->readSource(); }
        catch (\Throwable $error) { $state=null; $source=null; }
        echo json_encode(['nonce'=>$nonce,'page_id'=>'research:rq001_phase_i','revision'=>$source['revision']??null,
            'available'=>(bool)$state && (bool)$source && $source['revision']===$state[1]['revision'] && $source['raw_sha256']===$state[1]['raw_sha256'],
            'release'=>$state[0]['release']??null,'registry_sha256'=>$state[0]['registry_sha256']??null,
            'local_preview'=>$this->preview(),'private_preview'=>$state?(bool)$this->privatePreview():false]);
    }

    // Learning-only dispatch. The existing RQ-001 handlers are unchanged.
    public function displayLearning($event,$param) {
        global $ID;
        if (!is_string($ID) || !preg_match('/^mathematics_learning:higher_category_theory:synthetic_category_theory:(foundations|size|categories|functors|natural_transformations|yoneda|adjunctions|equivalences)$/D',$ID)) return;
        $original=$event->data;
        try {
            require_once __DIR__.'/learning.php';
            ILabLearningExplanation::display($event);
        } catch (\Throwable $error) { $event->data=$original; }
    }
    public function statusLearning($event,$param) {
        if ($event->data!=='ilabexplain_learning_status') return;
        $event->preventDefault(); $event->stopPropagation();
        header('Content-Type: application/json'); header('Cache-Control: no-store, private, max-age=0');
        header('Vary: Cookie'); header('X-Content-Type-Options: nosniff');
        try { require_once __DIR__.'/learning.php'; echo json_encode(ILabLearningExplanation::status(),JSON_THROW_ON_ERROR); }
        catch (\Throwable $error) { echo '{"available":false}'; }
    }
}
