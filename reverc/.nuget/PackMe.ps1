# Example of packing a project. For more, type 'Get-Help PowerPack' after importing the module.
# The individual functions also have help available.
Import-Module .\PowerPack -Force

# Get latest version of NuGet into this folder: nuget restore requires at least v2.7.
Invoke-NuGetDownload

Find-File "*.sln" | Invoke-NuGetRestore

Find-Project "Foo*" | Get-Project | Update-NuSpecDependencies | Invoke-DeepClean |
    Invoke-MSBuild | Invoke-NuGetPack | Invoke-NuGetPush -NuGetFeed "LocalNuGetFeed"
