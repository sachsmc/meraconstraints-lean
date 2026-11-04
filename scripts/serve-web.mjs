import { createServer } from "node:http";
import { existsSync, readFileSync, statSync } from "node:fs";
import { dirname, extname, join, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";
const site = resolve(dirname(dirname(fileURLToPath(import.meta.url))), "_site");
const port = Number(process.env.PORT || 8000);
const types = { ".html":"text/html; charset=utf-8", ".css":"text/css", ".js":"text/javascript", ".json":"application/json", ".svg":"image/svg+xml", ".png":"image/png", ".woff2":"font/woff2", ".bmp":"image/bmp", ".wasm":"application/wasm" };
createServer((req,res) => {
  try {
    const path = decodeURIComponent(new URL(req.url, "http://localhost").pathname);
    let file = resolve(site, "." + path);
    if (file !== site && !file.startsWith(site + sep)) { res.writeHead(403); res.end(); return; }
    if (existsSync(file) && statSync(file).isDirectory()) {
      if (!path.endsWith("/")) { res.writeHead(302, {Location:path+"/"}); res.end(); return; }
      file = join(file,"index.html");
    }
    if (!existsSync(file)) { res.writeHead(404); res.end("Not found"); return; }
    res.writeHead(200, {"Content-Type":types[extname(file)] || "text/plain; charset=utf-8"});
    res.end(readFileSync(file));
  } catch { res.writeHead(400); res.end("Bad request"); }
}).listen(port,"127.0.0.1",()=>console.log(`Preview: http://127.0.0.1:${port}/`));
