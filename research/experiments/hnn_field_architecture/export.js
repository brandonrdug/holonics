// Inspect the shared presentation and export its actual rendered vector surfaces.
// NODE_PATH must resolve Playwright. This is display/QA, never native Holonic computation.
const { chromium } = require('playwright');
const fs = require('node:fs');
const path = require('node:path');
(async () => {
 const [preview,destination]=process.argv.slice(2);
 if(!preview||!destination)throw new Error('usage: node export.js preview.html output-directory');
 fs.mkdirSync(destination,{recursive:true});
 const browser=await chromium.launch({headless:true});
 const page=await browser.newPage({viewport:{width:768,height:1100},deviceScaleFactor:1});
 const errors=[];page.on('pageerror',e=>errors.push(e.message));
 await page.goto('file://'+path.resolve(preview));await page.waitForTimeout(400);
 const frame=page.frames()[1];
 async function fit(){const h=await frame.evaluate(()=>document.body.scrollHeight);await page.locator('iframe').evaluate((e,h)=>e.style.height=h+'px',h);}
 async function exportSvg(selector,name){
  const vector=await frame.locator(selector).evaluate(svg=>{
   const clone=svg.cloneNode(true),originals=[svg,...svg.querySelectorAll('*')],copies=[clone,...clone.querySelectorAll('*')];
   originals.forEach((node,i)=>{const s=getComputedStyle(node);for(const key of ['fill','stroke','stroke-width','opacity','font-family','font-size','font-weight'])copies[i].style.setProperty(key,s.getPropertyValue(key));});
   const view=svg.viewBox.baseVal;clone.setAttribute('xmlns','http://www.w3.org/2000/svg');clone.setAttribute('width',view.width);clone.setAttribute('height',view.height);
   const paint=document.createElement('span');paint.style.background='var(--background)';document.body.append(paint);
   const bg=document.createElementNS('http://www.w3.org/2000/svg','rect');bg.setAttribute('width',view.width);bg.setAttribute('height',view.height);bg.setAttribute('fill',getComputedStyle(paint).backgroundColor);paint.remove();clone.prepend(bg);
   return new XMLSerializer().serializeToString(clone);
  });fs.writeFileSync(path.join(destination,name),vector+'\n');
 }
 await frame.locator('[data-focus=whole]').click();await fit();
 await page.screenshot({path:path.join(destination,'overview.png'),fullPage:true});
 for(const [s,n] of [['.field-diagram','architecture.svg'],['.receiver-face','receiver-face.svg'],['.receiver-entropy','receiver-entropy.svg']])await exportSvg(s,n);
 const checks=[];for(const focus of ['reception','contact','interior','generation','receiver']){
  await frame.locator(`[data-focus=${focus}]`).click();checks.push(await frame.locator(`[data-focus=${focus}]`).getAttribute('aria-pressed')==='true');
 }
 await frame.locator('[data-play]').click();await page.waitForTimeout(750);
 const playingIndex=Number(await frame.locator('[data-time-slider]').inputValue());
 await frame.locator('[data-play]').click();await page.waitForTimeout(180);
 const pausedIndex=Number(await frame.locator('[data-time-slider]').inputValue());
 if(playingIndex<1||playingIndex!==pausedIndex)throw new Error('play/pause failed');
 await frame.locator('[data-time-slider]').focus();await frame.locator('[data-time-slider]').press('End');
 if((await frame.locator('[data-time]').textContent())!=='2')throw new Error('proper clock did not update');
 await fit();await page.screenshot({path:path.join(destination,'receiver-later.png'),fullPage:true});
 await page.setViewportSize({width:360,height:1100});await page.waitForTimeout(250);await fit();
 await page.screenshot({path:path.join(destination,'narrow.png'),fullPage:true});
 const overflow=await frame.evaluate(()=>document.body.scrollWidth>innerWidth);
 if(errors.length||overflow||checks.some(x=>!x))throw new Error(JSON.stringify({errors,overflow,checks}));
 console.log(JSON.stringify({errors,overflow,operationSelections:checks.length,playPause:true,clockAndAperture:true,vector:'architecture.svg'}));
 await browser.close();
})();
