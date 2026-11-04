# Source-transcription audit only. The mathematical certificates are checked by Lean.
$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
$repoRoot = Split-Path -Parent $PSScriptRoot
$tex = Get-Content -Raw -LiteralPath (Join-Path $repoRoot 'sources/manuscript/appendix.tex')
$lean = Get-Content -Raw -LiteralPath (Join-Path $repoRoot 'MeraConstraints/Examples/InstrumentalAppendix.lean')
$rOutput = Get-Content -Raw -LiteralPath (Join-Path $repoRoot 'sources/rscripts/output/01-iv.txt')

function Integers([string] $value) {
    @([regex]::Matches($value, '-?\d+') | ForEach-Object { [int]$_.Value })
}

function Same([string] $label, $actual, $expected) {
    if (($actual -join ',') -cne ($expected -join ',')) {
        throw "$label differs between source representations."
    }
    Write-Output "$label agrees ($($actual.Count) entries)."
}

function LeanMatrix([string] $name) {
    $match = [regex]::Match($lean, "def $name\b[^\r\n]*:=\s*!!\[([\s\S]*?)\]")
    if (-not $match.Success) { throw "Missing Lean matrix $name" }
    Integers $match.Groups[1].Value
}

function LeanVector([string] $name) {
    $match = [regex]::Match($lean, "def $name\b[^\r\n]*:=\s*!\[([^\]]*)\]")
    if (-not $match.Success) { throw "Missing Lean vector $name" }
    Integers $match.Groups[1].Value
}

$section = [regex]::Match($tex, '\\section\{Details of instrumental variable example\}([\s\S]*?)\\section\{Proofs\}')
if (-not $section.Success) { throw 'Missing Appendix B IV section' }
$matrices = [regex]::Matches($section.Groups[1].Value, '\\begin\{pmatrix\}([\s\S]*?)\\end\{pmatrix\}')
if ($matrices.Count -ne 4) { throw 'Expected B, coordinate table, Hi and He' }
$texB = @(Integers $matrices[0].Groups[1].Value)
$texHi = @(Integers $matrices[2].Groups[1].Value)
$texHe = @(Integers $matrices[3].Groups[1].Value)
if ($texB.Count -ne 128 -or $texHi.Count -ne 96 -or $texHe.Count -ne 16) {
    throw 'Unexpected printed matrix dimensions'
}
Same 'B: Lean / LaTeX' @(LeanMatrix 'printedB') $texB
Same 'Hi: Lean / LaTeX' @(LeanMatrix 'printedHi') $texHi
Same 'He: Lean / LaTeX' @(LeanMatrix 'printedHe') $texHe

foreach ($pair in @(@('printedUpper', 'b_i'), @('printedTarget', 'b_e'))) {
    $match = [regex]::Match($section.Groups[1].Value, "$($pair[1]) = \(([^)]*)\)")
    if (-not $match.Success) { throw "Missing $($pair[1])" }
    Same "$($pair[0]): Lean / LaTeX" @(LeanVector $pair[0]) @(Integers $match.Groups[1].Value)
}

$coordinates = @(Integers $matrices[1].Groups[1].Value)
if ($coordinates.Count -ne 24) { throw 'Expected eight coordinate triples' }
$semanticOrder = @(for ($i = 0; $i -lt 8; $i++) {
    $coordinates[3 * $i + 2]; $coordinates[3 * $i]; $coordinates[3 * $i + 1]
})
$rowMatch = [regex]::Match($lean, 'def rowIndex\b[\s\S]*?:=\s*!\[([^\]]*)\]')
$leanOrder = @([regex]::Matches($rowMatch.Groups[1].Value, '\b(false|true)\b') |
    ForEach-Object { if ($_.Value -eq 'true') { 1 } else { 0 } })
Same '(X,Y,Z) to (Z,X,Y) row order' $leanOrder $semanticOrder

$rB = [regex]::Match($rOutput, '==== Matrix B[^\r\n]*====([\s\S]*?)Dimensions:')
$rRows = @{}
foreach ($row in [regex]::Matches($rB.Groups[1].Value, '(?m)^\s*\[(\d+),\]\s*([^\r\n]+)')) {
    $index = [int]$row.Groups[1].Value
    if (-not $rRows.ContainsKey($index)) { $rRows[$index] = @() }
    $rRows[$index] += @(Integers $row.Groups[2].Value)
}
if ($rRows.Count -ne 8) { throw 'Expected eight R matrix rows' }
foreach ($row in $rRows.Values) { if ($row.Count -ne 16) { throw 'Expected sixteen R columns' } }
$rFlatB = @(for ($i = 1; $i -le 8; $i++) { $rRows[$i] })
Same 'B: LaTeX / stored R output' $texB $rFlatB

$rH = [regex]::Match($rOutput, '==== H-representation[^\r\n]*====([\s\S]*?)attr\(')
$rHi = @(); $rHe = @(); $rUpper = @(); $rTarget = @()
foreach ($row in [regex]::Matches($rH.Groups[1].Value, '(?m)^\s*\[\s*\d+,\]\s*([^\r\n]+)')) {
    $values = @(Integers $row.Groups[1].Value)
    if ($values.Count -ne 10) { throw 'Expected ten rcdd entries per row' }
    $coefficients = @($values[2..9] | ForEach-Object { -$_ })
    if ($values[0] -eq 0) { $rHi += $coefficients; $rUpper += $values[1] }
    elseif ($values[0] -eq 1) { $rHe += $coefficients; $rTarget += $values[1] }
    else { throw 'Unexpected rcdd equality flag' }
}
Same 'Hi: LaTeX / rcdd (-A sign convention)' $texHi $rHi
Same 'He: LaTeX / rcdd (-A sign convention)' $texHe $rHe
Same 'Upper bounds: Lean / rcdd' @(LeanVector 'printedUpper') $rUpper
Same 'Equality targets: Lean / rcdd' @(LeanVector 'printedTarget') $rTarget
Write-Output 'Appendix B source-transcription audit passed; mathematical H exactness is checked separately in Lean.'
