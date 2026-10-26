$LakeArguments = $args
$ErrorActionPreference = 'Stop'
$localToolchain = Join-Path $PSScriptRoot '..\work\lean-tools\elan\toolchains\leanprover--lean4---v4.24.0\bin'
$localLake = Join-Path $localToolchain 'lake.exe'
if (Test-Path -LiteralPath $localLake) {
    $env:PATH = $localToolchain + [System.IO.Path]::PathSeparator + $env:PATH
    $lakeExecutable = $localLake
} else {
    $lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
    if ($null -eq $lakeCommand) {
        $elanLake = Join-Path $env:USERPROFILE '.elan\bin\lake.exe'
        if (-not (Test-Path -LiteralPath $elanLake)) {
            throw 'Install Lean with elan, or add lake to PATH, before running this script.'
        }
        $lakeExecutable = $elanLake
    } else {
        $lakeExecutable = $lakeCommand.Source
    }
}

Push-Location $PSScriptRoot
try {
    & $lakeExecutable @LakeArguments
    $lakeExitCode = $LASTEXITCODE
} finally {
    Pop-Location
}
exit $lakeExitCode
