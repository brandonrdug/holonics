// Inspect the interactive construction and export the same vector drawing for the paper.
const {chromium}=require('playwright');
const fs=require('node:fs');const path=require('node:path');
(async()=>{
 const [preview,out,qa=out]=process.argv.slice(2);fs.mkdirSync(out,{recursive:true});fs.mkdirSync(qa,{recursive:true});
 const browser=await chromium.launch({headless:true});
 const page=await browser.newPage({viewport:{width:1200,height:1000},deviceScaleFactor:1});
 const errors=[];page.on('pageerror',e=>errors.push(e.message));
 await page.goto('file://'+path.resolve(preview));await page.waitForTimeout(500);
 const f=page.frames()[1];
 async function fit(){await page.locator('iframe').evaluate((e,h)=>e.style.height=h+'px',await f.evaluate(()=>document.body.scrollHeight));}
 async function vector(name){
  const xml=await f.locator('.engine-diagram').evaluate(svg=>{
   const copy=svg.cloneNode(true),orig=[svg,...svg.querySelectorAll('*')],dest=[copy,...copy.querySelectorAll('*')];
   orig.forEach((e,i)=>{const s=getComputedStyle(e);for(const k of ['fill','stroke','stroke-width','opacity','font-family','font-size','font-weight'])dest[i].style.setProperty(k,s.getPropertyValue(k));});
   copy.setAttribute('xmlns','http://www.w3.org/2000/svg');copy.setAttribute('width',svg.viewBox.baseVal.width);copy.setAttribute('height',svg.viewBox.baseVal.height);
   return new XMLSerializer().serializeToString(copy);
  });fs.writeFileSync(path.join(out,name),xml+'\n');
 }
 const checks=[];
 for(const m of ['network','generation','training','encoding']){
  await f.locator(`button[data-mode=${m}]`).click();await fit();
  checks.push(await f.locator(`button[data-mode=${m}]`).getAttribute('aria-pressed')==='true');
  if(['network','training'].includes(m))await vector(m+'.svg');
 }
 await f.locator('button[data-mode=network]').click();await fit();await page.screenshot({path:path.join(qa,'wide.png'),fullPage:true});
 const layouts=[];
 for(const w of [768,360]){
  await page.setViewportSize({width:w,height:1100});await page.waitForTimeout(200);await fit();
  layouts.push(await f.evaluate(()=>({width:innerWidth,overflow:document.body.scrollWidth>innerWidth})));
  await page.screenshot({path:path.join(qa,'width-'+w+'.png'),fullPage:true});
 }
 if(errors.length||checks.some(x=>!x)||layouts.some(x=>x.overflow))throw new Error(JSON.stringify({errors,checks,layouts}));
 console.log(JSON.stringify({errors,checks,layouts}));await browser.close();
})();
