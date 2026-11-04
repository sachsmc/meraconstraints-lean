import { copyFileSync, existsSync, lstatSync, mkdirSync, readFileSync, realpathSync, rmSync, writeFileSync } from "node:fs";
import { dirname, join, delimiter } from "node:path";
import { fileURLToPath } from "node:url";
import { spawn } from "node:child_process";
import { assemble, files } from "./assemble-web.mjs";
import { checkSite } from "./check-web.mjs";
import { ensureWindowsHeaders, prepareWindowsVersoAssets, finishWindowsVersoAssets } from "./setup-windows-docs.mjs";

const root = dirname(dirname(fileURLToPath(import.meta.url)));
const pinned = join(root, ".tools", "lean-4.31.0-windows", "bin");
const lake = existsSync(join(pinned, "lake.exe")) ? join(pinned, "lake.exe") : "lake";
const env = { ...process.env, MATHLIB_NO_CACHE_ON_UPDATE: "1", LEAN_NUM_THREADS: process.env.LEAN_NUM_THREADS || "2" };
const pathKey = Object.keys(env).find(k => k.toLowerCase() === "path") || "PATH";
if (existsSync(pinned)) env[pathKey] = pinned + delimiter + (env[pathKey] || "");
ensureWindowsHeaders(pinned);
// leansqlite's pinned build invokes "cc". Keep the compatibility alias local
// to the workspace's bundled Windows toolchain; no global tool is changed.
if (process.platform === "win32" && existsSync(join(pinned, "leanc.exe")) && !existsSync(join(pinned, "cc.exe"))) {
  copyFileSync(join(pinned, "leanc.exe"), join(pinned, "cc.exe"));
}

async function run(args, capture = false) {
  console.log(`\n> lake ${args.join(" ")}`);
  return new Promise((resolve, reject) => {
    const child = spawn(lake, args, { cwd: root, env, stdio: capture ? ["ignore", "pipe", "inherit"] : "inherit", windowsHide: true });
    let output = "";
    if (capture) child.stdout.on("data", chunk => {
      output += chunk;
      if (args.includes("query")) process.stdout.write(chunk);
    });
    child.on("error", reject);
    child.on("close", code => code === 0 ? resolve(output.trim()) : reject(new Error(`lake exited ${code}`)));
  });
}

for (const path of [join(root,"MeraConstraints.lean"), ...files(join(root,"MeraConstraints")).filter(p=>p.endsWith(".lean"))]) {
  if (/\b(sorry|admit|axiom)\b/.test(readFileSync(path,"utf8"))) throw new Error(`Proof placeholder in ${path}`);
}
await run(["-R", "-Kenv=dev", "build", "MeraConstraints", "@doc-gen4/doc-gen4"]);
const audit = await run(["-Kenv=dev", "env", "lean", "MeraConstraints/Test/Smoke.lean"], true);
const expected = readFileSync(join(root, "MeraConstraints/Test/Smoke.lean"), "utf8").match(/^#print axioms /gm)?.length || 0;
const blocks = [...audit.matchAll(/depends on axioms:\s*\[([^\]]*)\]/g)];
const count = blocks.length + [...audit.matchAll(/does not depend on any axioms/g)].length;
const allowed = new Set(["propext", "Classical.choice", "Quot.sound"]);
for (const block of blocks) for (const entry of block[1].split(/\s*,\s*/).filter(Boolean)) {
  if (!allowed.has(entry.trim())) throw new Error(`Unexpected proof dependency: ${entry}`);
}
if (!expected || count !== expected) throw new Error(`Incomplete proof audit: ${count}/${expected}`);
console.log(`Proof audit passed: ${count} declarations, standard logical dependencies only.`);
prepareWindowsVersoAssets();
let bookOutput;
try {
  bookOutput = await run(["-Kenv=dev", "query", ":literateHtml"], true);
} catch (error) {
  if (process.platform !== "win32") throw error;
  console.log("Retrying cached Verso extraction with one Lean worker after a Windows failure.");
  env.LEAN_NUM_THREADS = "1";
  bookOutput = await run(["-Kenv=dev", "query", ":literateHtml"], true);
}
const book = bookOutput.split(/\r?\n/).map(x => x.trim()).filter(x => existsSync(join(x, "index.html"))).at(-1);
if (!book) throw new Error("Verso did not return an HTML directory");
finishWindowsVersoAssets(book);

// The public doc-gen4 prefix command analyzes all imported project modules in
// one environment. Dependency-library API pages are not regenerated.
const apiBuild = join(root, ".lake/build/project-api");
if (existsSync(apiBuild)) {
  if (lstatSync(apiBuild).isSymbolicLink() || !realpathSync(apiBuild).startsWith(realpathSync(root) + (process.platform === "win32" ? "\\" : "/"))) {
    throw new Error("API output must stay inside the project workspace");
  }
  rmSync(apiBuild, { recursive: true });
}
mkdirSync(apiBuild, { recursive: true });
await run(["-Kenv=dev", "exe", "doc-gen4", "genCore", "--build", apiBuild, "MeraConstraints", "api-docs.db"]);
await run(["-Kenv=dev", "exe", "doc-gen4", "fromDb", "--build", apiBuild, join(apiBuild,"api-docs.db")]);
await run(["-Kenv=dev", "exe", "doc-gen4", "headerData", "--build", apiBuild]);
const record = { toolchain: "leanprover/lean4:v4.31.0", auditedDeclarations: count, builtAt: new Date().toISOString(), apiScope: "MeraConstraints (dependency APIs are not bundled)" };
await assemble(book, join(apiBuild, "doc"), record);
checkSite(join(root, "_site"));
writeFileSync(join(root, ".lake/build/website-build.json"), JSON.stringify(record, null, 2) + "\n");
console.log("\nWebsite ready in _site/. Preview: node scripts/serve-web.mjs");
