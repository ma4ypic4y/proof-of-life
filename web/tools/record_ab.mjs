// Short tweet clip of the A/B soups: node record_ab.mjs <out.webm> [seconds=16]
import puppeteer from "puppeteer-core";
const [,, out, secs = "16"] = process.argv;
const url = new URL("../dist/preview.html", import.meta.url).href;
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const browser = await puppeteer.launch({ executablePath: "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome", headless: "new", args: ["--hide-scrollbars"] });
const page = await browser.newPage();
await page.setViewport({ width: 1200, height: 700, deviceScaleFactor: 1.5 });
await page.emulateMediaFeatures([{ name: "prefers-color-scheme", value: "dark" }]);
await page.goto(url, { waitUntil: "networkidle2" });
await page.evaluate(() => document.fonts.ready);
// scroll so the two panels' captions sit at the top of the viewport
await page.evaluate(() => { const el = document.querySelector("#live .ab"); window.scrollTo(0, el.getBoundingClientRect().top + scrollY - 12); });
await sleep(800);
const box = await page.evaluate(() => { const r = document.querySelector("#live .ab").getBoundingClientRect(); return { x: r.x, y: r.y, w: r.width, h: Math.min(r.height, innerHeight - r.y) }; });
console.log(JSON.stringify(box));
const rec = await page.screencast({ path: out });
await sleep(1200);
await page.evaluate(() => document.getElementById("soup-play").click());
await sleep(+secs * 1000);
await rec.stop();
await browser.close();
