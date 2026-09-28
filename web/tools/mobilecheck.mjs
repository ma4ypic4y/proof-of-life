import puppeteer from "puppeteer-core";
const url = new URL("../dist/preview.html", import.meta.url).href;
const browser = await puppeteer.launch({ executablePath: "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome", headless: "new" });
const page = await browser.newPage();
await page.setViewport({ width: 400, height: 860, deviceScaleFactor: 2, isMobile: true });
page.on("pageerror", (e) => console.log("pageerror:", e.message));
await page.goto(url, { waitUntil: "networkidle2" });
await new Promise((r) => setTimeout(r, 2000));
const r = await page.evaluate(() => {
  const W = document.documentElement.clientWidth, wide = [];
  for (const el of document.querySelectorAll("body *")) {
    const b = el.getBoundingClientRect();
    if (b.right > W + 1 && !el.closest(".table-wrap, pre, .glyphs")) wide.push(`${el.tagName}.${el.className} right=${Math.round(b.right)}`);
  }
  return { scrollW: document.documentElement.scrollWidth, W, wide: wide.slice(0, 12) };
});
console.log(JSON.stringify(r, null, 1));
await page.screenshot({ path: "../.shots/mobile.png", fullPage: false });
await browser.close();
