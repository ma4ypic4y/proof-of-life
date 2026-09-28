// Render media/video/scene.html frame by frame: node render_video.mjs <out_dir> [t1,t2,... preview times]
import puppeteer from "puppeteer-core";
import fs from "fs";
const [,, outDir, preview] = process.argv;
fs.mkdirSync(outDir, { recursive: true });
const browser = await puppeteer.launch({ executablePath: "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome", headless: "new" });
const page = await browser.newPage();
await page.setViewport({ width: 1920, height: 1080, deviceScaleFactor: 1 });
page.on("pageerror", (e) => console.log("pageerror:", e.message));
page.on("console", (m) => { if (m.type() === "error") console.log("console:", m.text()); });
await page.goto("http://localhost:8765/media/video/scene.html#capture", { waitUntil: "networkidle0" });
await page.waitForFunction(() => window.READY === true, { timeout: 60000 });
console.log("events in collision run:", await page.evaluate(() => window.EVENT_COUNT));
const { DURATION, FPS } = await page.evaluate(() => ({ DURATION: window.DURATION, FPS: window.FPS }));
const times = preview ? preview.split(",").map(Number) : Array.from({ length: Math.round(DURATION * FPS) }, (_, i) => i / FPS);
let i = 0;
for (const t of times) {
  await page.evaluate((t) => window.render(t), t);
  await page.screenshot({ path: `${outDir}/${String(i).padStart(5, "0")}.png`, clip: { x: 0, y: 0, width: 1920, height: 1080 } });
  i++;
}
console.log("frames:", i);
await browser.close();
