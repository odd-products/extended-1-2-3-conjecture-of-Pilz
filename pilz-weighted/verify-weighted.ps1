param([switch] $HashesOnly)
$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
    $manifestPath = Join-Path $PSScriptRoot 'SOURCE_MANIFEST.sha256'
    if (-not (Test-Path -LiteralPath $manifestPath -PathType Leaf)) {
        throw 'Missing SOURCE_MANIFEST.sha256; release integrity cannot be verified.'
    }
    $verifiedFiles = 0
    if (Test-Path -LiteralPath $manifestPath) {
        foreach ($manifestLine in Get-Content -LiteralPath $manifestPath) {
            if ($manifestLine -notmatch '^([0-9a-f]{64})  (.+)$') {
                throw "Malformed source manifest line: $manifestLine"
            }
            $expectedHash = $Matches[1]
            $relativePath = $Matches[2]
            if ([System.IO.Path]::IsPathRooted($relativePath) -or $relativePath.Contains(':') -or
                @($relativePath.Replace('\', '/').Split('/')) -contains '..') {
                throw "Unsafe source manifest path: $relativePath"
            }
            $sourcePath = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot $relativePath))
            if (-not $sourcePath.StartsWith($PSScriptRoot + [System.IO.Path]::DirectorySeparatorChar,
                [System.StringComparison]::OrdinalIgnoreCase)) { throw 'Source path leaves the release directory.' }
            $actualHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $sourcePath).Hash.ToLowerInvariant()
            if ($actualHash -ne $expectedHash) { throw "Source checksum mismatch: $sourcePath" }
            $verifiedFiles += 1
        }
    }
    Write-Output "Verified $verifiedFiles source manifest entries."
    if ($HashesOnly) { return }
    & (Join-Path $PSScriptRoot 'lake.ps1') build WeightedPilz
    if ($LASTEXITCODE -ne 0) { throw 'WeightedPilz build failed.' }
    & (Join-Path $PSScriptRoot 'lake.ps1') env lean WeightedPilzFinalChecks.lean
    if ($LASTEXITCODE -ne 0) { throw 'WeightedPilz exact-type or transitive-axiom checks failed.' }
    & (Join-Path $PSScriptRoot 'lake.ps1') env lean WeightedPilzChecks.lean
    if ($LASTEXITCODE -ne 0) { throw 'WeightedPilz compact regression checks failed.' }
} finally {
    Pop-Location
}
