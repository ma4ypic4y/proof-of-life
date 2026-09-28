import puppeteer from "puppeteer-core";
const browser = await puppeteer.launch({ executablePath: "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome", headless: "new" });
const page = await browser.newPage();
page.on("pageerror", (e) => console.log("pageerror:", e.message));
for (const [w, name] of [[1280, "landing"], [400, "landing_mobile"]]) {
  await page.setViewport({ width: w, height: 900, isMobile: w < 500, deviceScaleFactor: 1 });
  await page.goto("http://localhost:8765/docs/", { waitUntil: "networkidle2" });
  await new Promise((r) => setTimeout(r, 1200));
  const sw = await page.evaluate(() => document.documentElement.scrollWidth);
  console.log(name, "scrollWidth", sw);
  await page.screenshot({ path: `../.shots/${name}.png`, fullPage: true });
}
for (const p of ["proof/", "life/"]) { await page.setViewport({ width: 1280, height: 900 }); await page.goto(`http://localhost:8765/docs/${p}`, { waitUntil: "networkidle2" }); console.log(p, "loaded", await page.title()); }
await browser.close();
