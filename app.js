'use strict';
const $=s=>document.querySelector(s),esc=x=>String(x??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const iconPaths={copy:'<rect x="8" y="8" width="12" height="12" rx="2"/><path d="M16 8V4H4v12h4"/>',download:'<path d="M12 3v12m-5-5 5 5 5-5M4 16v5h16v-5"/>',prev:'<path d="m14 6-6 6 6 6"/>',next:'<path d="m10 6 6 6-6 6"/>',chevron:'<path d="m6 9 6 6 6-6"/>',arrow:'<path d="M5 12h14m-5-5 5 5-5 5"/>',check:'<path d="m5 12.5 4.5 4.5L19 7.5"/>',minus:'<path d="M6 12h12"/>'};
const icon=name=>`<svg class="icon" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">${iconPaths[name]}</svg>`;
const fmt=(x,n=3)=>x===null||x===undefined||x===''?'—':Number(x).toLocaleString('en-US',{maximumFractionDigits:n});
const fixed=(x,n=3)=>x===null||x===undefined||x===''||!Number.isFinite(Number(x))?'—':Number(x).toFixed(n);
function sciHtml(x){if(x===null||x===undefined)return 'Not estimable';if(x>0&&x<.001){const [m,p]=Number(x).toExponential(2).split('e');return `${m} × 10<sup>${String(Number(p)).replace('-','−')}</sup>`}return fmt(x,4)}
// Edition, from <html data-edition="...">. Without the attribute (local server page) the page renders as v9.
// "lab" also shows the long-read NMD calls and the long-read counts by donor.
// "publication" shows no genotype quality (GQ, DP); its data export also drops donor IDs, GQ and DP.
const EDITION=document.documentElement.dataset.edition||'',LAB=EDITION==='lab',QUALITY=EDITION!=='publication';
let lrDonors=[];// Long-read donors in count order, from the info record: [{id, label}].
const cells=['iNCs','iPSC','UDC'],cellName=c=>c==='iPSC'?'iPSCs':c==='UDC'?'UDCs':c;
const peType=e=>({CE:'Cassette exon',ES:'Exon skipping',Alt5_pro:"Alternative 5′ inclusion",Alt5_dis:"Alternative 5′ exclusion",Alt3_pro:"Alternative 3′ inclusion",Alt3_dis:"Alternative 3′ exclusion",AI_intron_up:'Alternative intron inclusion',AI_spliced_up:'Alternative intron exclusion'}[e.PE_direction]||e.PE_direction);
const gtf=x=>({detected_by_GTF:'Annotated NMD',novel:'Novel',unsafe:'Coding overlap'}[x]||'Not available');
const strandLabel=x=>x==='-'?'−':x;
const biotypeLabel=x=>({protein_coding:'protein coding',nonsense_mediated_decay:'NMD',non_stop_decay:'non-stop decay',protein_coding_LoF:'protein coding LoF',retained_intron:'retained intron',protein_coding_CDS_not_defined:'CDS not defined'}[x]||String(x||'unknown').replaceAll('_',' '));
const biotypeColor=x=>x==='protein_coding'?'#3d5470':['nonsense_mediated_decay','non_stop_decay'].includes(x)?'#875a1f':'#5b6d68';
const geneKey=()=>String(current.gene_id).split('.')[0];
const routeBadge=v=>`<span class="badge ${v.route==='sQTL'?'purple':''}">${v.route==='SNP'?'SNP / indel':'sQTL'}</span>`;
// Variant evidence: Significant = main support (BH q < 0.05 plus the strict filters). Set only = exact carrier/PE-donor match.
const mainRule=v=>v.route==='sQTL'?'BH q < 0.05, no uncovered donor and strictly monotonic medians':'BH q < 0.05 and no uncovered PE donor';
const evidenceLabel=v=>v.category==='Set only'?'Set only':v.selected?'Significant':'Not significant';
const evidenceTitle=v=>v.category==='Set only'?'Variant carriers match the PE-positive donors exactly':v.selected?mainRule(v)+(v.set_agreement?'; carriers also match the PE-positive donors':''):'Main rule not met: '+mainRule(v);
function missedRule(v){
  if(v.selected||v.q===null||v.q===undefined||v.q>=.05)return '';
  const why=[];
  if(Number(v.n_uncovered)>0)why.push(`${fmt(v.n_uncovered,0)} uncovered ${Number(v.n_uncovered)===1?'donor':'donors'}`);
  if(v.route==='sQTL'&&v.mono_adj===false)why.push('medians not strictly monotonic across dosage groups');
  return why.length?`<p class="note">BH q &lt; 0.05, but not significant under the main rule: ${why.join('; ')}.</p>`:'';
}
let current=null,lrData=null,lrIndex=0,lrKind='best',lrOffset=0,variantIndex=0,searchToken=0,eventToken=0,lrToken=0,searchTimer;
let results={},found=[],gencodeMode='off',gencodeToken=0;const isoformCache={};
const signed=x=>x===null||x===undefined?'—':(x>0?'+':'')+fmt(x,0);
function medianLabel(e){return fixed(e.positive_median_dpsi)+(e.positive_median_missing_n?' *':'')}
function stopContext(e){
 const isTrue=x=>String(x).toLowerCase()==='true';
 if(e.NMD_scoring_mechanism==='normal_stop_3UTR')return "Canonical stop with a downstream 3′ UTR junction";
 if(e.NMD_scoring_mechanism==='stop_boundary')return "Translated stop after a coding-boundary change";
 if(isTrue(e.ptc_found)||['PTC','ptc_found'].includes(e.explain_ptc_status)){
  if(isTrue(e.ptc_within_pe))return "Predicted PTC inside the PE interval";
  if(String(e.ptc_within_pe).toLowerCase()==='false')return isTrue(e.frameshift)?"Frameshift with a PTC outside the PE interval":"Predicted PTC outside the PE interval";
  return "Predicted PTC; location unavailable";
 }
 if(e.NMD_assessment_status==='evaluated_CDS')return "CDS models assessed; no PTC found";
 if(e.explain_site_region==='5UTR')return "5′ UTR context; see the separate uORF assessment";
 if(e.explain_site_region==='3UTR')return "3′ UTR context; no qualifying coding-stop result";
 return "No applicable reference evaluation";
}
function uorfContext(e){
 const labels={potential_uORF_NMD:'Potential uORF-mediated NMD',uORF_NMD_not_supported:'uORF-mediated NMD not supported'};
 const states={not_required_CDS_available:'Not required: CDS model available',partial_or_unavailable:'Incomplete or unavailable assessment',not_applicable:'No applicable 5′ UTR reference'};
 return labels[e.uorf_label]||states[e.uorf_status]||'Not assessed';
}
// Static data: JSON files under ATLAS_DATA_URL (set in config.js). Each file loads once.
const DATA_URL=String(window.ATLAS_DATA_URL||'data/').replace(/\/*$/,'/'),dataCache={};
function getJSON(path){
 if(!dataCache[path])dataCache[path]=fetch(DATA_URL+path).then(r=>{
   if(!r.ok)throw new Error(r.status===404?'This PE is not in the published data.':'Unable to load data (HTTP '+r.status+').');
   return r.json();
 },e=>{console.error('PE Atlas data request failed:',DATA_URL+path,e);throw new Error('Unable to reach the PE Atlas data. Try again later.')}).catch(e=>{delete dataCache[path];throw e});
 return dataCache[path];
}
// File name of one record: cell and event ID joined by two underscores.
const recordFile=key=>encodeURIComponent(key.replace(':','__'))+'.json';
async function api(path,args={}) {
 let value;
 if(path==='info') value=await getJSON('info.json');
 else if(path==='event') value=await getJSON('events/'+recordFile(args.key));
 else if(path==='isoforms') value=await getJSON('isoforms/'+encodeURIComponent(args.gene)+'.json');
 else if(path==='lr') {
   const src=(await getJSON('lr/'+recordFile(args.key)))[args.kind||'best'],offset=Number(args.offset||0);
   value=src&&(src.available?{...src,offset,candidates:src.candidates.slice(offset,offset+10)}:src);
 } else if(path==='search') {
   const index=await getJSON('search.json');
   let q=(args.q||'').toLowerCase().trim();
   if(/chr[^ ]*:\d+[: _-]+[acgt]+[>: _/-]+[acgt]+/.test(q))q=q.replace(/[^a-z0-9]/g,'');
   const terms=q.split(/\s+/).filter(Boolean),offset=Number(args.offset||0);
   const found=index.filter(e=>(!args.cell||e.cell_type===args.cell)&&terms.every(t=>e.search.includes(t))&&(!args.evidence||e.evidence.includes(args.evidence)));
   value={total:found.length,offset,results:found.slice(offset,offset+40)};
 }
 if(value===undefined||value===null)throw new Error('This PE is not in the published data.');
 return JSON.parse(JSON.stringify(value));
}

function error(el,e){el.innerHTML='<div class="error">'+esc(e.message)+'</div>'}
function save(blob,name){const a=document.createElement('a');a.href=URL.createObjectURL(blob);a.download=name;a.click();setTimeout(()=>URL.revokeObjectURL(a.href),5000)}
let toastTimer,sectionFrame,jumpTarget=null;
function toast(message){clearTimeout(toastTimer);$('#toast').textContent=message;$('#toast').classList.add('visible');toastTimer=setTimeout(()=>$('#toast').classList.remove('visible'),3000)}
async function copyLocus(){
  const text=current.PE_junction;
  try{
    if(navigator.clipboard?.writeText)await navigator.clipboard.writeText(text);
    else throw new Error('Clipboard fallback');
    toast('Copied '+text);return;
  }catch(_){
    const focus=document.activeElement,field=document.createElement('textarea');field.value=text;field.className='clipboard-field';document.body.append(field);field.select();
    let copied=false;try{copied=document.execCommand('copy')}catch(_){}finally{field.remove();focus?.focus({preventScroll:true})}
    toast(copied?'Copied '+text:'Select the locus text to copy it.');
  }
}
function updateSectionNav(){
  sectionFrame=null;const nav=$('.section-nav');if(!nav)return;
  const buttons=[...nav.querySelectorAll('[data-jump]')],edge=nav.getBoundingClientRect().bottom+28;
  let active=buttons[0];
  for(const b of buttons)if(document.getElementById(b.dataset.jump).getBoundingClientRect().top<=edge)active=b;
  if(window.scrollY>0&&Math.ceil(window.innerHeight+window.scrollY)>=document.documentElement.scrollHeight-2)active=buttons.at(-1);
  if(jumpTarget)active=buttons.find(b=>b.dataset.jump===jumpTarget)||active;
  buttons.forEach(b=>{const on=b===active;b.classList.toggle('active',on);if(on)b.setAttribute('aria-current','location');else b.removeAttribute('aria-current')});
}
function scheduleSectionNav(){if(!sectionFrame)sectionFrame=requestAnimationFrame(updateSectionNav)}
window.addEventListener('scroll',scheduleSectionNav,{passive:true});window.addEventListener('resize',scheduleSectionNav);
// Honor an explicit jump even when a short section cannot reach the viewport top.
function clearJumpTarget(){jumpTarget=null;scheduleSectionNav()}
window.addEventListener('wheel',clearJumpTarget,{passive:true});window.addEventListener('touchstart',clearJumpTarget,{passive:true});
document.addEventListener('pointerdown',e=>{if(!e.target.closest('.section-nav'))clearJumpTarget()},{passive:true});
document.addEventListener('keydown',e=>{if(['ArrowUp','ArrowDown','PageUp','PageDown','Home','End',' '].includes(e.key)&&!e.target.closest('input,textarea,select'))clearJumpTarget()});
function countChip(n){return `<span class="count${Number(n)?'':' zero'}">${fmt(n,0)}</span>`}
function recordButton(e,attr,index){return `<button class="result ${current?.key===e.key?'active':''}" ${attr}="${index}" aria-pressed="${current?.key===e.key}"><strong class="result-gene">${esc(e.gene_name)}</strong><span class="result-median" title="Median directional ΔPSI among positive donors"><strong>${medianLabel(e)}</strong><small>median ΔPSI</small></span><span class="coordinate">${esc(e.PE_junction)}</span><span class="result-meta">${esc(peType(e))} · NMD tier ${esc(e.nmd_tier)}${String(e.main_selected).toLowerCase()==='false'?' · ClinVar candidate':''} · ${fmt(e.n_genotyping,0)}/${fmt(e.n_catalog,0)} donors</span></button>`}
function drawSearch(){
  const focused=document.activeElement,focusedKey=focused?.hasAttribute('data-result')?found[Number(focused.dataset.result)]?.key:null;
  found=[];
  $('#results').innerHTML=cells.map(cell=>{const d=results[cell];return `<div class="cell-column${d?.total?'':' is-empty'}"><h3>${cellName(cell)} ${countChip(d?.total)}</h3><div class="cell-results">${d?.results.length?d.results.map(e=>{let i=found.push(e)-1;return recordButton(e,'data-result',i)}).join(''):'<p class="empty-line">No matching PEs</p>'}</div>${d&&d.results.length<d.total?`<button class="more" data-more="${cell}">Show more</button>`:''}</div>`}).join('');
  document.querySelectorAll('[data-result]').forEach(b=>b.onclick=()=>openEvent(found[Number(b.dataset.result)].key));
  document.querySelectorAll('[data-more]').forEach(b=>b.onclick=()=>runSearch(b.dataset.more));
  if(focusedKey){const index=found.findIndex(e=>e.key===focusedKey);document.querySelector(`[data-result="${index}"]`)?.focus({preventScroll:true})}
}
async function runSearch(moreCell=null){
  const token=++searchToken,q=$('#search').value,evidence=$('#evidence').value;
  $('#results').setAttribute('aria-busy','true');$('#search-status').textContent='Searching…';$('#resetSearch').classList.add('hidden');
  try{
    const wanted=moreCell?[moreCell]:cells;
    const ds=await Promise.all(wanted.map(cell=>api('search',{q,evidence,cell,offset:moreCell?results[cell].results.length:0})));
    if(token!==searchToken)return;
    wanted.forEach((cell,i)=>{results[cell]=moreCell?{...ds[i],results:results[cell].results.concat(ds[i].results)}:ds[i]});
    const total=cells.reduce((n,cell)=>n+(results[cell]?.total||0),0);
    $('#search-status').textContent=total?`${fmt(total,0)} matching cell-specific ${total===1?'record':'records'}`:'No matches. Try another gene, coordinate or evidence filter.';
    $('#resetSearch').classList.toggle('hidden',total>0||(!q&&!evidence));
    document.querySelectorAll('[data-query]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.query.toLowerCase()===q.trim().toLowerCase()&&!evidence)));
    drawSearch();if(!current&&found.length)openEvent(found[0].key);
  }catch(e){if(token===searchToken){error($('#results'),e);$('#search-status').textContent='Search could not load. Change the search to try again.'}}
  finally{if(token===searchToken)$('#results').setAttribute('aria-busy','false')}
}
function kpi(label,value,sub='',cls=''){return `<div class="kpi ${cls}"><div class="kpi-label">${label}</div><div class="kpi-value">${value}</div>${sub?`<div class="kpi-sub">${sub}</div>`:''}</div>`}
function title(name,aside=''){return `<div class="section-title"><h2>${name}</h2>${aside}</div>`}
// An empty section collapses to one line: its title and a short status.
function emptySection(section,content,message){$(section).classList.add('is-empty');const c=$(content);c.className='';c.innerHTML=`<p class="empty-line">${message}</p>`}
// Gene annotation: the seven Fig. S5 categories, in figure order and colors. Each chip opens its source evidence.
const ANNOTATIONS={
  disease:{label:'Disease gene',color:'#F97F5F',rule:'Linked to an OMIM phenotype with a MIM number, or to an Orphanet disorder.',source:'OMIM genemap2, generated 27 Oct 2025 · Orphanet gene–disorder list'},
  lof:{label:'LoF gene',color:'#3C9BC9',rule:'ClinGen haploinsufficiency score 3, or a G2P entry with a loss-of-function mechanism.',source:'ClinGen gene curation, 6 Oct 2025 · G2P, 6 Oct 2025'},
  hi:{label:'Haploinsufficient',color:'#65BDBA',rule:'ClinGen haploinsufficiency score 3, or a G2P loss-of-function entry with monoallelic autosomal inheritance.',source:'ClinGen gene curation, 6 Oct 2025 · G2P, 6 Oct 2025'},
  gof:{label:'GoF gene',color:'#32AEAE',rule:'A G2P entry with a gain-of-function mechanism.',source:'G2P, 6 Oct 2025'},
  cancer:{label:'Cancer gene',color:'#DC3972',rule:'Listed in the COSMIC Cancer Gene Census.',source:'COSMIC Cancer Gene Census v103, GRCh38'},
  dcrt:{label:'DCRT eligible',color:'#FAA26F',rule:'ASO-eligibility class 1 or 2 in the DCRT gene list.',source:'Dutch Center for RNA Therapeutics (DCRT) gene list'},
  dee:{label:'DEE gene',color:'#EE709F',rule:'Listed as a developmental and epileptic encephalopathy gene.',source:'Laboratory-curated DEE gene list'}};
const extLink=(href,text)=>`<a class="anno-id" href="${href}" target="_blank" rel="noopener noreferrer">${esc(text)}</a>`;
const plural=(n,word)=>`${fmt(n,0)} ${word}${n===1?'':'s'}`;
function annoList(items,limit=6){
  const ul=xs=>`<ul class="anno-list">${xs.join('')}</ul>`;
  return items.length<=limit?ul(items):ul(items.slice(0,limit))+`<details class="anno-more"><summary>Show ${fmt(items.length-limit,0)} more</summary>${ul(items.slice(limit))}</details>`;
}
// One evidence row. met: true/false marks a rule criterion; null for plain facts.
function annoRow(name,body,met=null){
  const mark=met===null?'':`<span class="anno-mark ${met?'met':'unmet'}" title="${met?'Meets this criterion':'Does not meet this criterion'}">${icon(met?'check':'minus')}<span class="visually-hidden">${met?'Meets:':'Does not meet:'}</span></span>`;
  return `<div class="anno-row"><dt>${mark}<span>${name}</span></dt><dd>${body}</dd></div>`;
}
function g2pEntries(a,test){
  if(!a.g2p)return a.g2p_mechanisms?`<span>Mechanisms: ${esc(a.g2p_mechanisms)}</span>`:'<span class="muted">No G2P entry</span>';
  const xs=a.g2p.filter(test);
  if(!xs.length)return '<span class="muted">No matching G2P entry</span>';
  return annoList(xs.map(x=>`<li><span class="anno-id">${esc(x.id)}</span><span>${esc(x.disease)}<span class="muted"> · ${esc(x.allelic.replaceAll('_',' '))} · ${esc(x.confidence)}</span></span></li>`));
}
function clingenText(c){
  if(!c?.score)return '<span class="muted">No ClinGen dosage record</span>';
  return `Haploinsufficiency score <strong>${esc(c.score)}</strong> · ${esc(c.description)}<span class="anno-sub">${[c.disease,c.evaluated&&'evaluated '+c.evaluated].filter(Boolean).map(esc).join(' · ')}</span>`;
}
const isLoF=x=>x.mechanism.toLowerCase().includes('loss of function'),isGoF=x=>x.mechanism.toLowerCase().includes('gain of function');
function annoEvidence(key,a){
  if(key==='disease'){
    const o=a.omim||{gene:[],phenotypes:[]},rows=[];
    if(o.phenotypes.length)rows.push(annoRow(`OMIM<small>${plural(o.phenotypes.length,'phenotype')}</small>`,`${o.gene.length?`<span class="anno-sub first">Gene MIM ${o.gene.map(m=>extLink('https://www.omim.org/entry/'+encodeURIComponent(m),m)).join(', ')}</span>`:''}${annoList(o.phenotypes.map(p=>`<li>${p.mim==='NA'?'<span class="anno-id">—</span>':extLink('https://www.omim.org/entry/'+encodeURIComponent(p.mim),'MIM '+p.mim)}<span>${esc(p.name)}${p.inheritance?`<span class="muted"> · ${esc(p.inheritance)}</span>`:''}</span></li>`))}`));
    if(a.orphanet?.length)rows.push(annoRow(`Orphanet<small>${plural(a.orphanet.length,'disorder')}</small>`,annoList(a.orphanet.map(d=>`<li>${extLink('https://www.orpha.net/en/disease/detail/'+encodeURIComponent(d.code),'ORPHA:'+d.code)}<span>${esc(d.name)}</span></li>`))));
    return rows.join('');
  }
  if(key==='lof'||key==='hi'){
    const c=a.criteria||{},hi=key==='hi';
    return annoRow('ClinGen',clingenText(a.clingen),!!c.clingen_hi3)+annoRow(hi?'G2P · monoallelic LoF':'G2P · LoF mechanism',g2pEntries(a,hi?x=>isLoF(x)&&x.allelic.toLowerCase().includes('monoallelic_autosomal'):isLoF),!!(hi?c.g2p_lof_monoallelic:c.g2p_lof));
  }
  if(key==='gof')return annoRow('G2P · GoF mechanism',g2pEntries(a,isGoF));
  if(key==='cancer'){
    const c=a.cosmic||{},role=String(c.role||'').split(';').map(x=>x.trim()).filter(Boolean).map(x=>({TSG:'Tumour suppressor (TSG)',oncogene:'Oncogene',fusion:'Fusion'}[x]||x)).join(' · ');
    const origin=[c.somatic&&'Somatic',c.germline&&'Germline'].filter(Boolean).join(' and ');
    return annoRow('Census tier',`Tier ${esc(c.tier||'—')}`)+annoRow('Role',esc(role||'—'))+annoRow('Mutation origin',esc(origin||'—'))+(c.somatic_tumours?annoRow('Somatic tumours',esc(c.somatic_tumours)):'')+(c.germline_tumours?annoRow('Germline tumours',esc(c.germline_tumours)):'');
  }
  if(key==='dcrt'){
    const d=a.dcrt||{};
    return annoRow('Eligibility class',`<strong>${esc(d.eligibility)}</strong>`)+(d.inheritance?annoRow('Inheritance',esc(d.inheritance)):'')+(d.phenotypes?annoRow('Phenotypes',`<span class="anno-wrap">${esc(d.phenotypes)}</span>`):'')+(d.comment?annoRow('Comment',esc(d.comment)):'')+(d.tango?annoRow('TANGO',esc(d.tango)):'')+(d.nat?annoRow('NAT',esc(d.nat)):'');
  }
  return annoRow('DEE list','Listed by gene symbol');
}
function geneAnnotation(e){
  const a=e.gene_annotation;if(!a)return '';
  const body=!a.available?'<span class="anno-none">Not available for this gene</span>':!a.hits.length?'<span class="anno-none">No disease or mechanism annotation</span>':
    a.hits.map(k=>`<button class="anno-chip" data-anno="${k}" aria-expanded="false" aria-controls="anno-panel"><span class="anno-dot" style="background:${ANNOTATIONS[k].color}" aria-hidden="true"></span>${ANNOTATIONS[k].label}${icon('chevron')}</button>`).join('');
  return `<div class="gene-annotation"><span class="anno-label">Gene annotation</span><div class="anno-chips">${body}</div></div><div id="anno-panel" class="anno-panel" role="region" hidden></div>`;
}
function toggleAnnotation(key){
  const panel=$('#anno-panel'),open=panel.dataset.key===key&&!panel.hidden,a=current.gene_annotation;
  document.querySelectorAll('[data-anno]').forEach(b=>b.setAttribute('aria-expanded',String(!open&&b.dataset.anno===key)));
  if(open){panel.hidden=true;panel.dataset.key='';panel.innerHTML='';return}
  const t=ANNOTATIONS[key];panel.dataset.key=key;panel.setAttribute('aria-label',t.label+' evidence');
  panel.innerHTML=`<div class="anno-head"><h3><span class="anno-dot" style="background:${t.color}" aria-hidden="true"></span>${t.label}</h3><p>${t.rule}</p></div><dl class="anno-grid">${annoEvidence(key,a)}</dl><p class="anno-source">Source: ${t.source}</p>`;
  panel.hidden=false;
}
async function openEvent(key){
  jumpTarget=null;
  const token=++eventToken;++lrToken;$('#main').innerHTML='<div class="welcome"><h2>Loading PE…</h2></div>';
  try{
    const e=await api('event',{key});if(token!==eventToken)return;current=e;gencodeMode='off';lrData=null;lrKind='best';lrOffset=0;variantIndex=0;
    history.replaceState(null,'','#pe='+btoa(key));drawSearch();
    const selected=e.variants.filter(v=>v.selected),clinical=new Set(e.clinvar.map(v=>v.ClinVar_ID)),others=e.related.filter(r=>r.key!==e.key);
    const frame=['3UTR','5UTR'].includes(e.explain_site_region)?'Not a CDS frame change':({outframe:'Frameshift',inframe:'In-frame',NA:'Not assessed'}[e.explain_frame_status]||'Not assessed');
    const share=Number(e.n_catalog)>0?Math.max(0,Math.min(1,Number(e.n_genotyping)/Number(e.n_catalog))):0;
    const nav=[['longread','Long-read structures',e.cell_type==='iNCs'?'':'<span class="nav-note">iNCs only</span>'],['variants','Variants',countChip(selected.length)],['clinical','ClinVar',countChip(clinical.size)],['related-section','Other PEs in gene',countChip(others.length)]];
    $('#main').innerHTML=`<section id="overview" class="record-head" aria-label="Overview"><div class="record-heading"><div class="record-identity"><h1>${esc(e.gene_name)}</h1><div class="chips"><span class="chip dark">${cellName(e.cell_type)}</span>${String(e.main_selected).toLowerCase()==='false'?'<span class="chip">ClinVar candidate · not a main representative</span>':''}</div></div><button id="copyLocus" class="quiet">${icon('copy')}Copy locus</button></div><p class="locus"><span class="mono">${esc(e.PE_junction)}</span><span>${esc(strandLabel(e.strand))} strand</span><span>${fmt(e.PE_length,0)} bp</span></p>${geneAnnotation(e)}
    <div class="kpis">${kpi('PE type',esc(peType(e)),'','text type')}${kpi('Median ΔPSI',medianLabel(e),'across positive donors','accent')}${kpi('Prevalence',fmt(e.n_genotyping,0)+'<span class="of"> / '+fmt(e.n_catalog,0)+'</span>',`positive donors<span class="meter" aria-hidden="true"><span style="width:${(share*100).toFixed(1)}%"></span></span>`)}${kpi('NMD tier',esc(e.nmd_tier||'—'))}${kpi('GTF overlap',esc(gtf(e.GTF_Predict)),'','text')}</div>
    ${e.positive_median_missing_n?`<p class="note">* Median available for ${e.positive_median_n} of ${e.positive_median_expected_n} positive donors.</p>`:''}<details id="predictionDetails" class="details"><summary>Reference-model prediction details</summary><dl class="meta-grid">${[['Annotation reference transcript',e.tier_tx_id||'Not recorded'],['Predicted reading frame',frame],['Predicted stop context',stopContext(e)],['uORF assessment',uorfContext(e)]].map(([k,v])=>`<div><dt>${k}</dt><dd>${esc(v)}</dd></div>`).join('')}</dl></details></section>
    <nav class="section-nav" aria-label="Sections">${nav.map(([id,label,extra])=>`<button data-jump="${id}">${label}${extra}</button>`).join('')}</nav>
    <section class="section" id="longread" tabindex="-1">${title('Long-read structures',gencodeControl(e))}<div id="lr-content"><p class="empty-line">Loading structures…</p></div></section>
    <section class="section" id="variants" tabindex="-1">${title('SNP / indel and sQTL')}<div id="variant-content"></div></section>
    <section class="section" id="clinical" tabindex="-1">${title('ClinVar')}<div id="clinvar-content"></div></section>
    <section class="section" id="related-section" tabindex="-1">${title('Other PEs in this gene')}<div id="related" class="cell-columns"></div></section>`;
    $('#copyLocus').onclick=copyLocus;
    document.querySelectorAll('[data-anno]').forEach(b=>b.onclick=()=>toggleAnnotation(b.dataset.anno));
    $('#anno-panel')?.addEventListener('keydown',ev=>{if(ev.key!=='Escape')return;const k=ev.currentTarget.dataset.key;toggleAnnotation(k);document.querySelector(`[data-anno="${k}"]`)?.focus()});
    document.querySelectorAll('[data-jump]').forEach(b=>b.onclick=()=>{jumpTarget=b.dataset.jump;const section=document.getElementById(jumpTarget);section.focus({preventScroll:true});section.scrollIntoView({behavior:matchMedia('(prefers-reduced-motion: reduce)').matches?'auto':'smooth'});scheduleSectionNav();});
    if(others.length){
      $('#related').innerHTML=cells.map(cell=>`<div class="cell-column"><h3>${cellName(cell)} ${countChip(others.filter(r=>r.cell_type===cell).length)}</h3><div class="cell-results">${e.related.map((r,i)=>r.cell_type===cell&&r.key!==e.key?recordButton(r,'data-related',i):'').join('')||'<p class="empty-line">None</p>'}</div></div>`).join('');
      document.querySelectorAll('[data-related]').forEach(b=>b.onclick=()=>openEvent(e.related[Number(b.dataset.related)].key));
    }else emptySection('#related-section','#related','No other PEs in this gene.');
    document.querySelectorAll('[data-gencode]').forEach(b=>b.onclick=()=>setGencode(b.dataset.gencode));
    renderVariants();renderClinvar();loadLR();scheduleSectionNav();
  }catch(e){if(token===eventToken)error($('#main'),e)}
}
async function loadLR(position=0){
  const focus=document.activeElement,restore=focus?.closest('#lr-content')?(focus.id?'#'+focus.id:focus.hasAttribute('data-kind')?`[data-kind="${focus.dataset.kind}"]`:null):null;
  const token=++lrToken,key=current.key;$('#lr-content').innerHTML='<p class="empty-line">Loading structures…</p>';
  try{const d=await api('lr',{key,kind:lrKind,offset:lrOffset});if(token!==lrToken||key!==current.key)return;lrData=d;lrIndex=Math.min(position,Math.max(0,(d.candidates?.length||0)-1));renderLR();if(restore&&document.activeElement===document.body)$(restore)?.focus({preventScroll:true});scheduleSectionNav()}
  catch(e){if(token===lrToken)error($('#lr-content'),e)}
}
function gencodeControl(e){
  const ref=e.main_transcript,n=e.gencode_isoforms_n||0;
  const b=(k,label,off)=>`<button data-gencode="${k}" class="${gencodeMode===k?'active':''}" aria-pressed="${gencodeMode===k}"${off?' disabled':''}>${label}</button>`;
  return `<div class="gencode-toggle" role="group" aria-label="GENCODE v48 transcripts"><span class="gencode-label">GENCODE</span><div class="segments">${b('off','Off')}${b('mane',esc(ref?.basis||'Reference'),!ref)}${b('all',`All isoforms<span class="seg-count">${fmt(n,0)}</span>`,!n)}</div></div>`;
}
async function setGencode(mode){
  const token=++gencodeToken,key=current.key,gene=geneKey();
  if(mode==='all'&&!isoformCache[gene]){
    try{const d=await api('isoforms',{gene});isoformCache[gene]=d.isoforms}catch(e){if(token===gencodeToken&&key===current.key)error($('#lr-content'),e);return}
  }
  if(token!==gencodeToken||key!==current.key)return;
  gencodeMode=mode;document.querySelectorAll('[data-gencode]').forEach(b=>{const on=b.dataset.gencode===mode;b.classList.toggle('active',on);b.setAttribute('aria-pressed',on)});
  if(lrData)renderLR();
}
function structureContainer(svg){return `<div class="structure-wrap" tabindex="0" role="region" aria-label="Transcript structures; scroll horizontally to see the full figure">${svg}</div><p class="figure-scroll-hint">Scroll horizontally to view the full structure.</p>`}
function referenceOnly(){if(gencodeMode==='off')return '';return current.main_transcript||gencodeMode==='all'&&isoformCache[geneKey()]?.length?structureContainer(structure(null)):'<p class="empty-line">No annotated reference transcript available.</p>'}
function renderLR(){
  const d=lrData;
  if(!d.available||!d.counts.pe_isoforms){$('#lr-content').innerHTML=referenceOnly()+'<p class="empty-line">'+(!d.available?'Long-read display covers main-catalog iNC records.':'No PE-state long-read isoform detected.')+'</p>';return}
  const c=d.counts,seg=(k,label,n)=>`<button class="${lrKind===k?'active':''}" data-kind="${k}" aria-pressed="${lrKind===k}">${label}${n===undefined?'':`<span class="seg-count">${fmt(n,0)}</span>`}</button>`;
  $('#lr-content').innerHTML=`<div class="toolbar"><div class="segments" role="group" aria-label="Structure category">${seg('best','Recommended')}${seg('single','Single-event pairs',c.single)}${seg('multi','Joint pairs',c.multi)}${seg('unpaired','Other isoforms',c.unpaired)}</div>${d.candidates.length?`<div class="pager"><button class="icon-btn" id="lrPrev" aria-label="Previous structure">${icon('prev')}</button><label><span class="pager-word">Structure</span> <input id="structureNumber" type="number" min="1" max="${d.total}" value="${d.offset+lrIndex+1}" aria-label="Structure number"> of ${fmt(d.total,0)}</label><button class="quiet" id="jumpStructure">Go</button><button class="icon-btn" id="lrNext" aria-label="Next structure">${icon('next')}</button></div>`:''}</div>
    ${d.candidates.length?'<div id="candidate-view"></div>':referenceOnly()+'<p class="empty-line">No structures in this category.</p>'}`;
  document.querySelectorAll('[data-kind]').forEach(b=>b.onclick=()=>{lrKind=b.dataset.kind;lrOffset=0;loadLR()});
  if(d.candidates.length){
    $('#lrPrev').onclick=()=>goStructure(d.offset+lrIndex-1);$('#lrNext').onclick=()=>goStructure(d.offset+lrIndex+1);
    $('#jumpStructure').onclick=()=>goStructure(Number($('#structureNumber').value)-1);
    $('#structureNumber').onkeydown=e=>{if(e.key==='Enter')$('#jumpStructure').click()};renderCandidate();
  }
}
function goStructure(index){
  if(!Number.isInteger(index)||index<0||index>=lrData.total){$('#structureNumber').value=lrData.offset+lrIndex+1;return}
  const offset=Math.floor(index/10)*10;
  if(offset===lrData.offset){lrIndex=index-offset;renderCandidate()}else{lrOffset=offset;loadLR(index-offset)}
}
function parseCoord(s){const m=s.match(/([^:]+):(\d+)-(\d+)/);return m?[m[1],Number(m[2]),Number(m[3])]:null}
function structure(candidate){
  const ref=gencodeMode!=='off'?current.main_transcript:null;
  const rows=[...(ref?[{model:ref,label:'GENCODE reference',sub:[ref.id,ref.basis],color:'#536579'}]:[]),...(candidate?.reference?[{model:candidate.reference,label:candidate.kind==='unpaired'?'Unpaired non-PE isoform':'Non-PE isoform',nmd:candidate.reference.nmd,color:'#8b9a96'}]:[]),...(candidate?[{model:candidate.pe,label:'PE isoform',nmd:candidate.pe.nmd,color:'#33755b'}]:[])];
  // All isoforms: the other GENCODE transcripts follow as compact rows. Every row uses the same axis X.
  const extra=gencodeMode==='all'?(isoformCache[geneKey()]||[]).filter(t=>t.id!==ref?.id):[];
  if(!rows.length&&!extra.length)return '';
  const events=candidate?.events||[current],target=parseCoord(current.PE_junction);
  const occupied=[...rows.flatMap(r=>r.model.exons),...extra.flatMap(t=>t.exons),...events.map(e=>parseCoord(e.PE_junction).slice(1))].sort((a,b)=>a[0]-b[0]),merged=[];
  occupied.forEach(([a,b])=>{if(merged.length&&a<=merged.at(-1)[1]+1)merged.at(-1)[1]=Math.max(merged.at(-1)[1],b);else merged.push([a,b])});
  const segments=[];let last=merged[0][0],pos=0;
  merged.forEach(([a,b])=>{if(a>last){const w=Math.min(65,a-last);segments.push([last,a,pos,w]);pos+=w}const w=b+1-a;segments.push([a,b+1,pos,w]);pos+=w;last=b+1});
  const X=v=>{const a=segments.find(s=>v>=s[0]&&v<=s[1])||segments.at(-1);return 245+(a[2]+(v-a[0])/(a[1]-a[0])*a[3])/pos*635};
  const top=40+rows.length*75,extraH=extra.length?30+extra.length*38:0,band=rows.length*75+(extra.length?extraH-10:0);
  const height=90+rows.length*75+extraH;
  let s=`<svg id="structure-svg" xmlns="http://www.w3.org/2000/svg" viewBox="0 0 930 ${height}" font-family="Arial, sans-serif" role="img" aria-label="${esc(current.gene_name)} transcript structures"><rect width="930" height="${height}" fill="#fbfcf9"/><text class="cap" x="245" y="22" font-size="12" fill="#5b6d68">${esc(target[0])} · ${esc(strandLabel(current.strand))} strand · introns compressed</text>`;
  events.forEach(e=>{const p=parseCoord(e.PE_junction),isTarget=e.event_id===current.event_id,x=X(p[1]),w=Math.max(2,X(p[2]+1)-x);s+=`<rect x="${x}" y="40" width="${w}" height="${band}" fill="${isTarget?'#cc3545':'#3e77bb'}" opacity=".15"/><line x1="${x}" x2="${x+w}" y1="37" y2="37" stroke="${isTarget?'#c92f40':'#3e77bb'}" stroke-width="${isTarget?3:2}" ${isTarget?'':'stroke-dasharray="3 2"'}><title>${isTarget?'Target PE':'Joint PE'}: ${esc(e.PE_junction)}</title></line>`});
  // One transcript line: intron line, strand arrows, exons, and the PE parts of exons in red (target) or blue (joint).
  const track=(m,y,h,color)=>{s+=`<line x1="${X(m.lo)}" x2="${X(m.hi+1)}" y1="${y}" y2="${y}" stroke="${color}"/>`;
    for(let x=X(m.lo)+25;x<X(m.hi)-5;x+=45){const sign=m.strand==='+'?1:-1;s+=`<path d="M${x-sign*3},${y-3} L${x},${y} L${x-sign*3},${y+3}" fill="none" stroke="${color}"/>`}
    m.exons.forEach(([a,b])=>{s+=`<rect x="${X(a)}" y="${y-h/2}" width="${Math.max(1,X(b+1)-X(a))}" height="${h}" fill="${color}"><title>${a}–${b}</title></rect>`;for(const e of [...events].sort((a,b)=>(a.event_id===current.event_id)-(b.event_id===current.event_id))){const p=parseCoord(e.PE_junction),aa=Math.max(a,p[1]),bb=Math.min(b,p[2]);if(aa<=bb)s+=`<rect x="${X(aa)}" y="${y-h/2}" width="${Math.max(2,X(bb+1)-X(aa))}" height="${h}" fill="${e.event_id===current.event_id?'#c92f40':'#3e77bb'}"/>`}})};
  rows.forEach((r,i)=>{const m=r.model,y=72+i*75;
    // The GENCODE row has a second line (transcript ID and basis). Long-read rows show their label alone,
    // except on the lab page, where the second line is the predicted NMD call.
    const sub=r.sub?r.sub.map((t,j)=>`<tspan x="14" dy="${j?'1.25em':0}">${esc(t)}</tspan>`).join(''):'',call=LAB&&r.nmd?nmdLine(r.nmd,y):'';
    s+=`<text class="lbl" x="14" y="${sub||call?y-3:y+5}" font-size="14" font-weight="bold" fill="#1d3532">${r.label}</text>${sub?`<text class="sub" x="14" y="${y+15}" font-size="12" fill="#5b6d68">${sub}</text>`:''}${call}`;track(m,y,16,r.color);
  });
  if(extra.length){
    s+=`<line x1="14" x2="916" y1="${top+8}" y2="${top+8}" stroke="#dbe3da"/><text class="cap" x="14" y="${top+26}" font-size="12" font-weight="bold" fill="#5b6d68">Other GENCODE isoforms · ${fmt(extra.length,0)}</text>`;
    extra.forEach((t,j)=>{const y=top+52+j*38,tags=t.tags.map(x=>x.replaceAll('_',' '));
      s+=`<g class="gencode-row"><title>${esc(t.id)} · ${esc(t.type)}${tags.length?' · '+esc(tags.join(', ')):''}</title><text class="lbl" x="14" y="${y-3}" font-size="13" font-weight="bold" fill="#1d3532">${esc(t.name)}</text><text class="sub" x="14" y="${y+13}" font-size="12" fill="${biotypeColor(t.type)}">${esc(biotypeLabel(t.type))}${t.tags.includes('MANE_Plus_Clinical')?' · MANE Plus Clinical':''}</text>`;track(t,y,12,'#536579');s+='</g>';
    });
  }
  s+=`<text class="cap" x="245" y="${height-16}" font-size="12" fill="#5b6d68">${fmt(merged[0][0],0)}</text><text class="cap" x="880" y="${height-16}" text-anchor="end" font-size="12" fill="#5b6d68">${fmt(merged.at(-1)[1],0)}</text></svg>`;return s;
}
function renderCandidate(){
  const p=lrData.candidates[lrIndex],a=p.pe,n=lrData.offset+lrIndex;
  $('#structureNumber').value=n+1;$('#lrPrev').disabled=n===0;$('#lrNext').disabled=n+1>=lrData.total;
  $('#candidate-view').innerHTML=`<div class="pair-facts"><span class="chip">${p.kind==='single'?'Single-event pair':p.kind==='multi'?'Joint pair':'Unpaired comparison'}</span>${p.mane?'<span class="chip mane" title="Same intron chain as the GENCODE MANE Select transcript. Transcript ends can differ.">Non-PE matches MANE Select</span>':''}<span>CHX increase in <strong>${fmt(a.up,0)} / 3</strong> donors</span></div>
    ${structureContainer(structure(p))}<div class="structure-foot"><div class="pe-coordinates">${p.events.map(e=>{const t=e.event_id===current.event_id,text=`<span class="${t?'target-label':'joint-label'}">${t?'Target PE':'Joint PE'}</span> <span class="mono">${esc(e.PE_junction)}</span> · ${esc(peType(e))}`;
      // A joint PE opens its own record; the hash link keeps browser Back working.
      return `<div><span class="swatch ${t?'target':'joint'}" aria-hidden="true"></span>${t||!e.key?text:`<a class="joint-link" href="#pe=${btoa(e.key)}" title="Open this joint PE">${text}${icon('arrow')}</a>`}</div>`}).join('')}</div><button id="downloadStructure" class="quiet">${icon('download')}Download SVG</button></div>
    ${p.kind==='unpaired'?'<p class="note">Unpaired isoforms may differ elsewhere.</p>':''}${LAB?lrCounts(p):''}`;
  $('#downloadStructure').onclick=()=>save(new Blob([$('#structure-svg').outerHTML],{type:'image/svg+xml'}),current.gene_name+'_structure_'+(n+1)+'.svg');
}
// Lab page: SQANTI3 predicted_NMD of each long-read isoform model (TRUE, FALSE or NA). NA is not FALSE.
const NMD_CALLS={TRUE:{word:'yes',color:'#875a1f'},FALSE:{word:'no',color:'#1d5a48'},NA:{word:'NA',color:'#596b63'}};
function nmdLine(x,y){
  const c=NMD_CALLS[x]||{word:String(x),color:'#596b63'},open=!(x in NMD_CALLS)||x==='NA';
  return `<g class="nmd-call" data-nmd="${esc(x)}"><title>SQANTI3 predicted_NMD: ${esc(x)}</title><circle cx="19" cy="${y+10.5}" r="4.5" fill="${open?'none':c.color}" stroke="${c.color}" stroke-width="1.5"/><text class="sub" x="29" y="${y+15}" font-size="12" fill="#5b6d68">Predicted NMD: <tspan font-weight="bold" fill="${c.color}">${esc(c.word)}</tspan></text></g>`;
}
// Signed number with a true minus sign. A value that rounds to zero shows as 0.
function signedNum(x,n){const r=Number(Number(x).toFixed(n));return r===0?(0).toFixed(n):(r>0?'+':'−')+Math.abs(r).toLocaleString('en-US',{minimumFractionDigits:n,maximumFractionDigits:n})}
const cpmText=x=>Number(x).toLocaleString('en-US',{minimumFractionDigits:2,maximumFractionDigits:2});
// Two decimals; a small non-zero value keeps its first significant digit, so its sign stays visible.
const log2Text=x=>signedNum(x,x===0||Math.abs(x)>=.01?2:1-Math.floor(Math.log10(Math.abs(x))));
// Lab page: long-read reads and CPM for each donor before (Ctrl) and after CHX, for each isoform drawn in the structure.
// counts and cpm run donor by donor, Ctrl then CHX. log2fc has one value per donor; it is null when the
// CHX-response table has no record for the isoform (some non-PE isoforms), and is then not recomputed.
function lrCounts(p){
  const donors=[0,1,2].map(i=>lrDonors[i]||{id:'Donor '+(i+1)}),num=(text,cls='')=>`<td class="num${cls?' '+cls:''}">${text}</td>`;
  const change=(x,n)=>num(signedNum(x,n),'change'+(signedNum(x,n)===(0).toFixed(n)?' zero':''));
  const isoforms=[[p.pe,'PE isoform','#33755b'],...(p.reference?[[p.reference,p.kind==='unpaired'?'Unpaired non-PE isoform':'Non-PE isoform','#8b9a96']]:[])];
  const group=([m,label,color])=>{
    const rows=donors.map((d,i)=>{
      const ctrl=m.counts[2*i],chx=m.counts[2*i+1],fc=m.log2fc[i],known=fc!==null&&fc!==undefined,up=known&&fc>0;
      return `<tr><th scope="row">${esc(d.id)}${d.label?`<small>${esc(d.label)}</small>`:''}</th>${num(fmt(ctrl,0),'grp')}${num(fmt(chx,0))}${change(chx-ctrl,0)}${num(cpmText(m.cpm[2*i]),'grp')}${num(cpmText(m.cpm[2*i+1]))}${change(m.cpm[2*i+1]-m.cpm[2*i],2)}<td class="num grp${up?' up':''}"${up?' title="Counts as a CHX increase"':known?'':' title="No CHX-response record for this isoform"'}>${known?log2Text(fc):'—'}</td></tr>`;
    }).join('');
    const total=k=>donors.reduce((n,_,i)=>n+m.counts[2*i+k],0);
    return `<tbody><tr class="lr-isoform"><th colspan="8" scope="rowgroup"><span class="lr-name"><span class="swatch" style="background:${color}" aria-hidden="true"></span>${label}<span class="mono">${esc(m.id)}</span></span></th></tr>${rows}<tr class="lr-total"><th scope="row">Total</th>${num(fmt(total(0),0),'grp')}${num(fmt(total(1),0))}${change(total(1)-total(0),0)}<td class="grp" colspan="3"></td><td class="grp"></td></tr></tbody>`;
  };
  return `<div class="lr-counts"><h3>Long-read counts by donor</h3><div class="lr-table-wrap" tabindex="0" role="region" aria-label="Long-read counts by donor; scroll horizontally on small screens"><table class="lr-table"><thead><tr><th rowspan="2" scope="col">Donor</th><th colspan="3" scope="colgroup" class="grp" title="Long reads assigned to the isoform model">Reads</th><th colspan="3" scope="colgroup" class="grp" title="Reads per million long reads in the library">CPM</th><th rowspan="2" scope="col" class="num grp" title="log₂((CHX CPM + 1) / (Ctrl CPM + 1)); a value above 0 counts as a CHX increase">log₂FC</th></tr><tr><th scope="col" class="num grp">Ctrl</th><th scope="col" class="num">CHX</th><th scope="col" class="num">Change</th><th scope="col" class="num grp">Ctrl</th><th scope="col" class="num">CHX</th><th scope="col" class="num">Change</th></tr></thead>${isoforms.map(group).join('')}</table></div></div>`;
}
function renderVariants(focus=false){
  const vs=current.variants;
  if(!vs.length){emptySection('#variants','#variant-content','No variant evidence for this PE.');return}
  $('#variant-content').innerHTML=`<div class="evidence-grid"><div class="table-scroll"><table><thead><tr><th>Variant</th><th>Evidence</th></tr></thead><tbody>${vs.map((v,i)=>`<tr class="pick ${i===variantIndex?'selected':''}" data-variant="${i}" tabindex="0"><td><span class="mono strong">${esc(v.variant)}</span>${routeBadge(v)}</td><td class="${v.selected?'evidence-yes':'muted'}" title="${esc(evidenceTitle(v))}">${evidenceLabel(v)}</td></tr>`).join('')}</tbody></table></div><div id="donor-view" class="plot"></div></div>`;
  document.querySelectorAll('[data-variant]').forEach(b=>{b.onclick=()=>{variantIndex=Number(b.dataset.variant);renderVariants()};b.onkeydown=ev=>{if(ev.key==='Enter'||ev.key===' '){ev.preventDefault();variantIndex=Number(b.dataset.variant);renderVariants(true)}}});
  if(focus)document.querySelector(`[data-variant="${variantIndex}"]`)?.focus();
  renderDonors();
}
function niceTicks(lo,hi){const raw=(hi-lo||1)/4,mag=10**Math.floor(Math.log10(raw)),step=[1,2,2.5,5,10].map(f=>f*mag).find(x=>x>=raw*.999),t=[];for(let v=Math.floor(lo/step);v<=Math.ceil(hi/step);v++)t.push(+(v*step).toFixed(6));return t}
function renderDonors(){
  const v=current.variants[variantIndex],ds=v.donors.filter(d=>d.dose!==null&&d.adj!==null&&d.adj!==undefined);
  $('#donor-view').innerHTML=`<div class="variant-head"><span class="mono">${esc(v.variant)}</span>${routeBadge(v)}</div><div class="stats"><div><span class="stat-label">Spearman ρ</span><span class="stat-value">${fmt(v.rho)}</span></div><div><span class="stat-label">BH q</span><span class="stat-value">${sciHtml(v.q)}</span></div><div><span class="stat-label">Donors</span><span class="stat-value">${fmt(ds.length,0)}</span></div></div>${missedRule(v)}<div id="donor-plot"></div>${ds.some(d=>d.state==='uncovered')?'<p class="note"><span class="dot" aria-hidden="true"></span> Gray points: uncovered donors (too few reads).</p>':''}<details class="details"><summary>${QUALITY?'Donor values and quality':'Donor values'}</summary><div class="table-scroll"><table><thead><tr><th>Donor</th><th class="num">ALT dosage</th><th class="num">ΔPSI</th>${QUALITY?'<th class="num">GQ</th><th class="num">DP</th>':''}</tr></thead><tbody>${v.donors.map(d=>`<tr><td>${esc(d.label)}</td><td class="num">${fmt(d.dose,0)}</td><td class="num">${fmt(d.adj)}</td>${QUALITY?`<td class="num">${fmt(d.gq,0)}</td><td class="num">${fmt(d.dp,0)}</td>`:''}</tr>`).join('')}</tbody></table></div></details>`;
  if(!ds.length){$('#donor-plot').innerHTML='<p class="empty-line">No donor values available.</p>';return}
  const ticks=niceTicks(Math.min(0,...ds.map(d=>d.adj)),Math.max(.1,...ds.map(d=>d.adj))),min=ticks[0],max=ticks.at(-1);
  const X=x=>80+x*145,Y=y=>240-(y-min)/(max-min)*196,color=v.route==='SNP'?'#2c887f':'#8471a1';
  let s='<svg viewBox="0 0 450 292" role="img" aria-label="ALT dosage and PE delta PSI">';
  ticks.forEach(y=>{s+=`<line x1="52" x2="424" y1="${Y(y)}" y2="${Y(y)}" stroke="${y===0?'#cfd8cc':'#e7ece5'}"/><text class="t" x="44" y="${Y(y)+4}" text-anchor="end" font-size="12" fill="#5b6d68">${y}</text>`});
  [0,1,2].forEach(dose=>{s+=`<text class="a" x="${X(dose)}" y="262" text-anchor="middle" font-size="13" fill="#3c514c">${dose}</text>`;const ys=ds.filter(d=>d.dose===dose).map(d=>d.adj).sort((a,b)=>a-b);if(ys.length){let med=ys.length%2?ys[Math.floor(ys.length/2)]:(ys[ys.length/2-1]+ys[ys.length/2])/2;s+=`<line x1="${X(dose)-24}" x2="${X(dose)+24}" y1="${Y(med)}" y2="${Y(med)}" stroke="#264c3c" stroke-width="2.5"/>`}});
  ds.forEach((d,i)=>{const jitter=((i*7)%11-5)*2;s+=`<circle tabindex="0" cx="${X(d.dose)+jitter}" cy="${Y(d.adj)}" r="5" fill="${d.state==='uncovered'?'#b0b9b3':color}" opacity=".85" stroke="white" stroke-width=".8"><title>${esc(d.label)} · ALT dosage ${d.dose} · ΔPSI ${d.adj}${QUALITY?` · GQ ${d.gq??'NA'} · DP ${d.dp??'NA'}`:''}</title></circle>`});
  s+=`<text class="a" x="238" y="285" text-anchor="middle" font-size="13" fill="#5b6d68">ALT dosage</text><text class="a" x="52" y="24" font-size="13" fill="#5b6d68">ΔPSI</text></svg>`;$('#donor-plot').innerHTML=s;
}
const sigClass=s=>{s=String(s).toLowerCase();return s.includes('pathogenic')?'path':s.includes('benign')?'benign':s.includes('uncertain')?'vus':''};
function renderClinvar(){
  const cs=current.clinvar;
  if(!cs.length){emptySection('#clinical','#clinvar-content','No matched ClinVar variants.');return}
  $('#clinvar-content').innerHTML=`<div class="table-scroll"><table><thead><tr><th>Variant / ClinVar ID</th><th>Clinical significance</th><th>SpliceAI score</th><th>Predicted splice site</th><th class="num">Site offset (bp)</th></tr></thead><tbody>${cs.map(c=>`<tr><td><span class="mono strong">${esc(c.Variant)}</span><a href="https://www.ncbi.nlm.nih.gov/clinvar/variation/${encodeURIComponent(c.ClinVar_ID)}/" target="_blank" rel="noopener noreferrer">ClinVar ${esc(c.ClinVar_ID)} ↗</a></td><td><span class="sig ${sigClass(c.ClinVar_Sig)}">${esc(String(c.ClinVar_Sig).replaceAll('_',' '))}</span></td><td><strong class="score">${fmt(c.Evidence_Channel_Score)}</strong> <span class="muted">${esc(c.Match_Type)}</span>${String(c.Score_Gene_Matches_PE).toLowerCase()==='false'?'<span class="warning-text">Score gene: '+esc(c.Gene)+' (different gene)</span>':''}</td><td class="mono">${esc(c.Chrom)}:${esc(c.Predicted_Splice_Pos)}</td><td class="num strong">${signed(c.variant_to_site_offset)}</td></tr>`).join('')}</tbody></table></div><p class="note">Site offset = predicted splice site − variant position, in genomic coordinates (not strand-adjusted).</p>`;
}
$('#search').oninput=()=>{clearTimeout(searchTimer);searchTimer=setTimeout(()=>runSearch(),250)};$('#evidence').onchange=()=>runSearch();
document.querySelectorAll('[data-query]').forEach(b=>b.onclick=()=>{clearTimeout(searchTimer);$('#search').value=b.dataset.query;$('#evidence').value='';current=null;runSearch()});
$('#resetSearch').onclick=()=>{clearTimeout(searchTimer);$('#search').value='';$('#evidence').value='';$('#search').focus();runSearch()};
$('#skipContent').onclick=e=>{e.preventDefault();$('#main').focus();$('#main').scrollIntoView()};
function hashKey(){try{return location.hash.startsWith('#pe=')?atob(location.hash.slice(4)):decodeURIComponent(location.hash.slice(1))}catch(_){return ''}}
// Joint-PE links and browser Back/Forward change the hash; show the new record from its top.
window.addEventListener('hashchange',async()=>{const key=hashKey();if(!key||key===current?.key)return;await openEvent(key);$('#main').focus({preventScroll:true});$('#overview')?.scrollIntoView({block:'start'})});
api('info').then(async d=>{lrDonors=d.lr_donors||[];$('#catalog-stats').textContent=d.main_events?fmt(d.main_events,0)+' main PEs · '+fmt(d.events,0)+' ClinVar candidates':fmt(d.events,0)+' PEs · '+fmt(d.genes,0)+' genes';const key=hashKey();if(key)await openEvent(key);runSearch()}).catch(e=>error($('#main'),e));
