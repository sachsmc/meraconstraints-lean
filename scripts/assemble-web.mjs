import { cpSync, existsSync, lstatSync, mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { dirname, join, relative, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";

const root = dirname(dirname(fileURLToPath(import.meta.url)));
const escape = s => s.replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll('"', "&quot;");
export function files(dir) { return readdirSync(dir, { withFileTypes: true }).flatMap(e => e.isDirectory() ? files(join(dir, e.name)) : [join(dir, e.name)]); }
function cleanOutput(path) {
  const target = resolve(path);
  if (target !== join(root, "_site")) throw new Error("Refusing to clear a path outside the website output");
  if (existsSync(target) && lstatSync(target).isSymbolicLink()) throw new Error("Website output must not be a symlink");
  rmSync(target, { recursive: true, force: true });
  mkdirSync(target);
}
function relativeAsset(page, target, html) {
  const url = new URL(relative(join(root, "_site"), page).split(sep).join("/"), "https://site.invalid/");
  const base = new URL(html.match(/<base\b[^>]*href="([^"]*)"/i)?.[1] || url.href, url);
  const baseDir = base.pathname.endsWith("/") ? base.pathname : dirname(base.pathname);
  return relative(baseDir, "/" + target).split(sep).join("/") || "./";
}
export async function assemble(book, api, record = {}) {
  if (!existsSync(join(book, "index.html")) || !existsSync(join(api, "index.html"))) throw new Error("Both generated sites are required");
  const site = join(root, "_site");
  cleanOutput(site);
  cpSync(book, site, { recursive: true });
  cpSync(api, join(site, "docs"), { recursive: true });
  cpSync(join(root, "site-assets/navigation.js"), join(site, "navigation.js"));
  cpSync(join(root, "site-assets/navigation.css"), join(site, "navigation.css"));
  for (const page of files(join(site, "docs")).filter(x => x.endsWith(".html"))) {
    let html = readFileSync(page, "utf8");
    const css = relativeAsset(page, "navigation.css", html);
    const js = relativeAsset(page, "navigation.js", html);
    if (relative(join(site,"docs"),page) !== "navbar.html") html = html.replace(/<\/head>/i, `<link rel="stylesheet" href="${css}"><script src="${js}" defer></script></head>`);
    const module = relative(join(site, "docs"), page).split(sep).join("/").replace(/\.html$/, "");
    if (module === "MeraConstraints" || module.startsWith("MeraConstraints/")) {
      const chapter = module === "MeraConstraints/Guide" ? "guide/" : module === "MeraConstraints/Scope" ? "scope/" : module + "/";
      const href = relativeAsset(page, chapter, html);
      html = html.replace(/<a href="#">source<\/a>/g, `<a href="${href}">source (literate chapter)</a>`);
    }
    // Imports of dependency modules live in the external Mathlib API.
    // Project links stay local and must pass the file checker.
    const pageUrl = new URL(relative(site,page).split(sep).join("/"),"https://site.invalid/");
    const baseUrl = new URL(html.match(/<base\b[^>]*href="([^"]*)"/i)?.[1] || pageUrl.href,pageUrl);
    html = html.replace(/\bhref="([^"]+)"/g,(whole,href) => {
      const target = new URL(href.replaceAll("&amp;","&"),baseUrl);
      if (target.origin !== pageUrl.origin) return whole;
      const dependency = target.pathname.match(/^\/docs\/((?:Mathlib|Init|Lean|Std|Lake|Batteries|Aesop|Qq|ProofWidgets|ImportGraph|LeanSearchClient|Plausible)(?:\/[^?#]*)?\.html)$/);
      return dependency ? `href="https://leanprover-community.github.io/mathlib4_docs/${dependency[1]}${target.search}${target.hash}"` : whole;
    });
    writeFileSync(page, html);
  }
  // Verso emits breadcrumb links to namespace folders without Lean modules.
  for (const namespace of ["Probability","SCM","Examples"]) {
    const dir = join(site,"MeraConstraints",namespace);
    const children = readdirSync(dir,{withFileTypes:true}).filter(e=>e.isDirectory() && existsSync(join(dir,e.name,"index.html")));
    writeFileSync(join(dir,"index.html"),`<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width"><title>${namespace} · MERA constraints</title><link rel="stylesheet" href="../../navigation.css"><script src="../../navigation.js" defer></script></head><body><main style="max-width:55rem;margin:3rem auto;padding:0 1rem;font:1rem/1.65 system-ui"><h1>${namespace}</h1><ul>${children.map(e=>`<li><a href="${e.name}/">${escape(e.name)}</a></li>`).join("")}</ul></main></body></html>`);
  }
  for (const [module,route] of [["Guide","guide"],["Scope","scope"]]) {
    const dir = join(site,"MeraConstraints",module);
    mkdirSync(dir,{recursive:true});
    writeFileSync(join(dir,"index.html"),`<!doctype html><html lang="en"><head><meta charset="utf-8"><meta http-equiv="refresh" content="0;url=../../${route}/"><title>${module}</title></head><body><a href="../../${route}/">Open ${module}</a></body></html>`);
  }
  const resources = join(site, "resources");
  mkdirSync(resources, { recursive: true });
  for (const name of ["README.md", "plan.md", "manuscript-issues.md", "NOTICE", "LICENSE", "lake-manifest.json", "lean-toolchain"]) cpSync(join(root, name), join(resources, name));
  writeFileSync(join(resources, "build.json"), JSON.stringify(record, null, 2) + "\n");
  writeFileSync(join(resources, "index.html"), `<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width"><title>Resources · MERA constraints</title><link rel="stylesheet" href="../navigation.css"><script src="../navigation.js" defer></script></head><body><main style="max-width:55rem;margin:3rem auto;padding:0 1rem;font:1rem/1.65 system-ui"><h1>Sources, scope and build record</h1><p>The book renders the checked Lean sources. Further numerical example certificates were skipped at the author's request; existing certificates are retained.</p><ul>${["README.md", "plan.md", "manuscript-issues.md", "build.json", "lake-manifest.json", "lean-toolchain", "NOTICE", "LICENSE"].map(n => `<li><a href="${escape(n)}">${escape(n)}</a></li>`).join("")}</ul></main></body></html>`);
  writeFileSync(join(site, ".nojekyll"), "");
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const recordPath = join(root,".lake/build/website-build.json");
  const record = existsSync(recordPath) ? JSON.parse(readFileSync(recordPath,"utf8")) : {};
  await assemble(resolve(process.argv[2] || ".lake/build/literate-html"), resolve(process.argv[3] || ".lake/build/project-api/doc"),record);
}
