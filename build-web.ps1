$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    node scripts/build-web.mjs
    if ($LASTEXITCODE -ne 0) { throw 'Website build failed' }
} finally {
    Pop-Location
}
