// node shot.mjs <out.png> [width=1280] [dark=1] [wait=2500]
import puppeteer from "puppeteer-core";
import { fileURLToPath } from "url";
const [,, out, width = "1280", dark = "1", wait = "2500"] = process.argv;
const url = new URL("../dist/preview.html", import.meta.url).href;
const browser = await puppeteer.launch({ executablePath: "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome", headless: "new", args: ["--hide-scrollbars"] });
const page = await browser.newPage();
await page.setViewport({ width: +width, height: 900 });
await page.emulateMediaFeatures([{ name: "prefers-color-scheme", value: dark === "1" ? "dark" : "light" }]);
page.on("pageerror", (e) => console.log("pageerror:", e.message));
await page.goto(url, { waitUntil: "networkidle2" });
await new Promise((r) => setTimeout(r, +wait));
await page.screenshot({ path: out, fullPage: true });
await browser.close();
