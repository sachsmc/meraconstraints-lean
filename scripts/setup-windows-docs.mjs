// Lean's minimal bundled C toolchain omits the general MinGW SDK headers.
// Provenance: https://github.com/leanprover/lean4/issues/10831
// Package manifest: https://packages.msys2.org/packages/mingw-w64-clang-x86_64-headers
import { cpSync, existsSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { createHash } from "node:crypto";
import { execFileSync } from "node:child_process";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const root = dirname(dirname(fileURLToPath(import.meta.url)));
const url = "https://mirror.msys2.org/mingw/clang64/mingw-w64-clang-x86_64-headers-14.0.0.r495.g63ebe6cdb-1-any.pkg.tar.zst";
const sha256 = "a84695c0e29b0659506b519f3ba9ebfd35e91641819b2fe9b7f453393c9adc87";
const llvmCommit = "35990504507d79e0b9deb809c8ee5e1b34ceef20"; // llvmorg-22.1.4
// Verso v4.31.0 strips a forward-slash prefix from embedded search assets.
// On Windows their names retain backslashes, so its writer first targets
// this workspace-local directory. Copy the canonical assets back afterwards.
export function prepareWindowsVersoAssets() {
  if (process.platform === "win32") mkdirSync(join(root,".lake/static-web/search"),{recursive:true});
}
export function finishWindowsVersoAssets(book) {
  if (process.platform === "win32") cpSync(join(root,".lake/packages/verso/static-web/search"),join(book,"-verso-search"),{recursive:true});
}
function ensurePthreadHeaders(include) {
  if (existsSync(join(include,"pthread_time.h"))) return;
  const url = "https://mirror.msys2.org/mingw/clang64/mingw-w64-clang-x86_64-winpthreads-14.0.0.r569.g34eeafb7d-1-any.pkg.tar.zst";
  const sha256 = "acf7ddfa35c0111ee7aa53b23187081f4478eb25c69afd6b67ff939616a23f5c";
  const sdk = join(root,".tools/pthread-headers"), archive = join(sdk,"headers.pkg.tar.zst");
  mkdirSync(sdk,{recursive:true});
  if (!existsSync(archive)) execFileSync("curl.exe",["-fL","--retry","2","--output",archive,url],{stdio:"inherit",windowsHide:true});
  if (createHash("sha256").update(readFileSync(archive)).digest("hex") !== sha256) throw new Error("Winpthreads header package checksum mismatch");
  // Extract only the known header subtree, never the package's libraries.
  execFileSync("tar.exe",["-xf",archive,"-C",sdk,"clang64/include"],{stdio:"inherit",windowsHide:true});
  for (const entry of readdirSync(join(sdk,"clang64/include"))) {
    if (!existsSync(join(include,entry))) cpSync(join(sdk,"clang64/include",entry),join(include,entry),{errorOnExist:true});
  }
  writeFileSync(join(sdk,"installed.json"),JSON.stringify({url,sha256,include},null,2)+"\n");
}
function ensureClangHeaders(include) {
  const destination = join(include,"clang");
  if (existsSync(join(destination,"x86intrin.h")) && existsSync(join(destination,"mm_malloc.h"))) return;
  const source = join(root,".tools/llvm-headers-source");
  const git = args => execFileSync("git",["-c",`safe.directory=${source.replaceAll("\\","/")}`,"-C",source,...args],{encoding:"utf8",windowsHide:true});
  if (!existsSync(join(source,".git"))) execFileSync("git",["clone","--depth","1","--branch","llvmorg-22.1.4","--filter=blob:none","--sparse","https://github.com/llvm/llvm-project.git",source],{stdio:"inherit",windowsHide:true});
  if (git(["rev-parse","HEAD"]).trim() !== llvmCommit) throw new Error("Unexpected LLVM header source revision");
  git(["sparse-checkout","set","clang/lib/Headers"]);
  function copyMissing(from,to) {
    mkdirSync(to,{recursive:true});
    for (const entry of readdirSync(from,{withFileTypes:true})) {
      const src = join(from,entry.name), dst = join(to,entry.name);
      if (entry.isDirectory()) copyMissing(src,dst);
      else if (entry.name.endsWith(".h") && !existsSync(dst)) cpSync(src,dst,{errorOnExist:true});
    }
  }
  copyMissing(join(source,"clang/lib/Headers"),destination);
  console.log(`Installed missing Clang 22.1.4 headers from LLVM ${llvmCommit}.`);
}
export function ensureWindowsHeaders(pinnedBin) {
  if (process.platform !== "win32" || !existsSync(join(pinnedBin, "leanc.exe"))) return;
  const include = resolve(pinnedBin, "../include");
  ensureClangHeaders(include);
  ensurePthreadHeaders(include);
  if (existsSync(join(include,"stdio.h")) && existsSync(join(include,"winsock2.h"))) return;
  const sdk = join(root,".tools/c-headers");
  const archive = join(sdk,"headers.pkg.tar.zst");
  mkdirSync(sdk,{recursive:true});
  if (!existsSync(archive)) execFileSync("curl.exe",["-fL","--retry","2","--output",archive,url],{stdio:"inherit",windowsHide:true});
  if (createHash("sha256").update(readFileSync(archive)).digest("hex") !== sha256) throw new Error("MinGW header package checksum mismatch");
  const entries = execFileSync("tar.exe",["-tf",archive],{encoding:"utf8",windowsHide:true}).split(/\r?\n/).filter(Boolean);
  for (const entry of entries) {
    if (/^(?:[/\\]|[A-Za-z]:)/.test(entry) || entry.replaceAll("\\","/").split("/").includes("..")) throw new Error("Unsafe header archive path");
  }
  execFileSync("tar.exe",["-xf",archive,"-C",sdk],{stdio:"inherit",windowsHide:true});
  // The package has no lean/ or clang/ subtrees. Preserve all existing headers.
  const headers = join(sdk,"clang64/include");
  for (const entry of readdirSync(headers)) {
    cpSync(join(headers,entry),join(include,entry),{recursive:true,force:false,errorOnExist:true});
  }
  writeFileSync(join(sdk,"installed.json"),JSON.stringify({url,sha256,include},null,2)+"\n");
  console.log("Installed verified MinGW headers in the workspace-local Lean toolchain.");
}
if (process.argv[1] && resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  ensureWindowsHeaders(join(root,".tools/lean-4.31.0-windows/bin"));
}
