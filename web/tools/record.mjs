// Records the demo video: node record.mjs <out.webm> [dark=1]   (needs ffmpeg on PATH)
import puppeteer from "puppeteer-core";
const [,, out, dark = "1"] = process.argv;
const url = new URL("../dist/preview.html", import.meta.url).href;
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const browser = await puppeteer.launch({ executablePath: "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome", headless: "new", args: ["--hide-scrollbars"] });
const page = await browser.newPage();
await page.setViewport({ width: 1280, height: 720, deviceScaleFactor: 1.5 });
if (dark === "1") await page.emulateMediaFeatures([{ name: "prefers-color-scheme", value: "dark" }]);
page.on("pageerror", (e) => console.log("pageerror:", e.message));
await page.goto(url, { waitUntil: "networkidle2" });
await page.evaluate(() => document.fonts.ready);
const scrollTo = async (sel, offset = 24, ms = 900) => {
  await page.evaluate(async (sel, offset, ms) => {
    const y0 = scrollY, y1 = document.querySelector(sel).getBoundingClientRect().top + scrollY - offset;
    const t0 = performance.now();
    await new Promise((res) => { const f = (t) => { const k = Math.min(1, (t - t0) / ms); const e = k < .5 ? 2 * k * k : 1 - (-2 * k + 2) ** 2 / 2; scrollTo(0, y0 + (y1 - y0) * e); k < 1 ? requestAnimationFrame(f) : res(); }; requestAnimationFrame(f); });
  }, sel, offset, ms);
};
const rec = await page.screencast({ path: out });
await sleep(2600);
if (await page.$("#film")) { await scrollTo("#film", 40, 900); await sleep(9000); }
await scrollTo("#watch .bench", 110);
await sleep(600);
await page.click("#hero-play");
await page.waitForFunction(() => document.getElementById("hero-result").textContent.startsWith("Done"), { timeout: 30000 });
await sleep(2400);
await page.select("#hero-speed", "40");
await page.click("#hero-next");
await sleep(500);
await page.click("#hero-play");
await page.waitForFunction(() => document.getElementById("hero-result").textContent.startsWith("Done"), { timeout: 30000 });
await sleep(2000);
await scrollTo("#atlas .plates", 90, 1200);
await sleep(1800);
await scrollTo("#atlas .plates", -420, 2600);
await sleep(800);
await scrollTo("#compare", 200, 1200);
await sleep(2200);
await scrollTo("#live .ab", 70, 1200);
await page.click("#soup-play");
await sleep(16000);
await scrollTo("#prompts .chart-box", 40, 1400);
await sleep(2500);
await scrollTo("#prompts .bench", 20, 1000);
await page.evaluate(async () => {
  const s = document.getElementById("ps-epoch"); const max = +s.max;
  for (let i = 0; i <= max; i++) { s.value = String(i); s.dispatchEvent(new Event("input")); await new Promise((r) => setTimeout(r, 6000 / (max + 1))); }
});
await sleep(1500);
await rec.stop();
await browser.close();
