import puppeteer from "puppeteer-core";
const url = new URL("../dist-proof/preview.html", import.meta.url).href;
const browser = await puppeteer.launch({ executablePath: "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome", headless: "new" });
const page = await browser.newPage();
await page.setViewport({ width: 1280, height: 900 });
await page.emulateMediaFeatures([{ name: "prefers-color-scheme", value: process.argv[2] || "dark" }]);
page.on("pageerror", (e) => console.log("pageerror:", e.message));
await page.goto(url, { waitUntil: "networkidle2" });
await new Promise((r) => setTimeout(r, 1200));
for (const [sel, f] of [[".hero", "p_hero"], ["#birth", "p_birth"], ["#wall", "p_wall"], ["#why", "p_why"], ["#theorems", "p_thm"]]) {
  const el = await page.$(sel); await el.screenshot({ path: `../.shots/${f}.png` });
}
await browser.close();
