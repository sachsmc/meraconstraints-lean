import { existsSync, readFileSync, statSync } from "node:fs";
import { dirname, join, relative, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";
import { files } from "./assemble-web.mjs";

export function checkSite(site) {
  site = resolve(site);
  for (const name of ["index.html", "guide/index.html", "scope/index.html", "docs/index.html", "resources/index.html", "docs/MeraConstraints/Completeness/StrongFaceSplitting.html", "docs/declarations/declaration-data.bmp", "docs/declarations/header-data.bmp", "docs/search.js"]) {
    if (!existsSync(join(site, name))) throw new Error(`Missing required page: ${name}`);
  }
  const htmlFiles = files(site).filter(x => x.endsWith(".html"));
  const broken = [];
  const targets = new Map();
  for (const file of htmlFiles) {
    const html = readFileSync(file, "utf8");
    const page = new URL(relative(site, file).split(sep).join("/"), "https://site.invalid/");
    const base = new URL(html.match(/<base\b[^>]*href="([^"]*)"/i)?.[1] || page.href, page);
    for (const match of html.matchAll(/\b(?:href|src)="([^"#]*)[^\"]*"/g)) {
      const href = match[1].replaceAll("&amp;", "&");
      if (!href || /^(?:mailto:|javascript:|data:)/i.test(href)) continue;
      const target = new URL(href, base);
      if (target.origin !== page.origin) continue;
      if (!targets.has(target.pathname)) {
        let local = join(site, decodeURIComponent(target.pathname));
        if (existsSync(local) && statSync(local).isDirectory()) local = join(local, "index.html");
        targets.set(target.pathname,existsSync(local));
      }
      if (!targets.get(target.pathname)) broken.push(`${relative(site,file)} → ${target.pathname}`);
    }
  }
  if (broken.length) throw new Error(`Broken local links (${broken.length}):\n${[...new Set(broken)].slice(0,30).join("\n")}`);
  const api = htmlFiles.filter(p => relative(site,p).split(sep).join("/").startsWith("docs/MeraConstraints"));
  if (api.length < 100) throw new Error(`API output is incomplete: ${api.length} project module pages`);
  console.log(`Website checks passed: ${htmlFiles.length} HTML pages, ${api.length} project API pages, no missing local links/assets.`);
}
if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  checkSite(resolve(process.argv[2] || join(dirname(dirname(fileURLToPath(import.meta.url))), "_site")));
}
