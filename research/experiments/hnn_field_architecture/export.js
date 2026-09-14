// Render the shared diagram in the bundled browser and export its actual vector surface.
// NODE_PATH must resolve Playwright. This is display/QA, never native Holonic computation.
const { chromium } = require('playwright');
const fs = require('node:fs');
const path = require('node:path');
(async () => {
 const [preview, destination] = process.argv.slice(2);
 if (!preview || !destination) throw new Error('usage: node export.js preview.html output-directory');
 fs.mkdirSync(destination,{recursive:true});
 const browser=await chromium.launch({headless:true});
 const page=await browser.newPage({viewport:{width:768,height:1000},deviceScaleFactor:1});
 const errors=[];page.on('pageerror',e=>errors.push(e.message));
 await page.goto('file://'+path.resolve(preview));
 await page.waitForTimeout(400);
 const frame=page.frames()[1];
 await frame.locator('[data-focus=whole]').click();
 await page.screenshot({path:path.join(destination,'overview.png'),fullPage:true});
 const vector=await frame.locator('svg.field-diagram').evaluate(svg=>{
  const clone=svg.cloneNode(true);
  const originals=[svg,...svg.querySelectorAll('*')];
  const copies=[clone,...clone.querySelectorAll('*')];
  originals.forEach((node,i)=>{
   const style=getComputedStyle(node);
   for(const key of ['fill','stroke','stroke-width','opacity','font-family','font-size','font-weight']) copies[i].style.setProperty(key,style.getPropertyValue(key));
  });
  clone.setAttribute('xmlns','http://www.w3.org/2000/svg');
  const view=svg.viewBox.baseVal;clone.setAttribute('width',view.width);clone.setAttribute('height',view.height);
  const paint=document.createElement('span');paint.style.background='var(--background)';document.body.append(paint);
  const background=document.createElementNS('http://www.w3.org/2000/svg','rect');
  background.setAttribute('width',view.width);background.setAttribute('height',view.height);
  background.setAttribute('fill',getComputedStyle(paint).backgroundColor);paint.remove();clone.prepend(background);
  return new XMLSerializer().serializeToString(clone);
 });
 fs.writeFileSync(path.join(destination,'architecture.svg'),vector+'\n');
 const checks=[];
 for(const focus of ['reception','contact','interior','generation']){
  await frame.locator(`[data-focus=${focus}]`).click();
  checks.push(await frame.locator(`[data-focus=${focus}]`).getAttribute('aria-pressed')==='true');
  if(focus==='contact')await page.screenshot({path:path.join(destination,'contact.png'),fullPage:true});
 }
 await page.setViewportSize({width:360,height:1100});await page.waitForTimeout(250);
 await page.screenshot({path:path.join(destination,'narrow.png'),fullPage:true});
 const overflow=await frame.evaluate(()=>document.body.scrollWidth>innerWidth);
 if(errors.length || overflow || checks.some(x=>!x))throw new Error(JSON.stringify({errors,overflow,checks}));
 console.log(JSON.stringify({errors,overflow,operationSelections:checks.length,vector:'architecture.svg'}));
 await browser.close();
})();
