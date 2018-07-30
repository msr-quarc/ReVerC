$source = @"
	using System;
	using System.Collections.Generic;
	using System.IO;
	using System.Linq;
	using System.Text;
	using System.Text.RegularExpressions;
	using System.Threading.Tasks;
	using System.Xml;
	using System.Xml.Linq;

    /// <summary>
    /// Read from the project's .csproj file.
    /// </summary>
    public class ConfigurationInfo
    {
        readonly Project Owner;

        public ConfigurationInfo(Project owner)
        {
            Owner = owner;
        }

        public string ConfigurationAndPlatform { get; set; }
        public string OutputPath { get; set; }
        public string Configuration { get; set; }
        public string Platform { get; set; }

        public string FullOutputPath
        {
            get
            {
                return Path.Combine(Owner.ProjectDirectory, OutputPath, Owner.OutputFileName);
            }
        }
    }

    /// <summary>
    /// Read from packages.config.
    /// </summary>
    public class PackageInfo
    {
        public string Id { get; set; }
        public string Version { get; set; }
        public string TargetFramework { get; set; }
    }

    public class Project
    {
        string avPattern = @"^\[assembly: AssemblyVersion\(""(.*)""\)\]";
        string afvPattern = @"^\[assembly: AssemblyFileVersion\(""(.*)""\)\]";
        //XmlNamespaceManager NsManager;

        public string FileName { get; private set; }
        public string Name { get; private set; }
        public string ProjectDirectory { get; private set; }
        public string NuSpecFileName { get; private set; }
		public string NuPkgFileName { get; set; }
        public string AssemblyInfoFileName { get; private set; }
        public string PackagesFileName { get; private set; }

        public XmlDocument ProjectXml { get; private set; }
        public string AssemblyName { get; private set; }
        public string OutputType { get; private set; }
        public Dictionary<string, ConfigurationInfo> Configurations { get; private set; }
        public List<PackageInfo> Packages { get; private set; }

        public Project(string fileName)
        {
            if (!File.Exists(fileName))
                throw new FileNotFoundException("The project file does not exist.", fileName);

            FileName = fileName;
            Name = Path.GetFileNameWithoutExtension(FileName);
            ProjectDirectory = Path.GetDirectoryName(FileName);

            var files = Directory.GetFiles(ProjectDirectory, "*.nuspec", SearchOption.AllDirectories);
            if (files != null && files.Length > 0)
                NuSpecFileName = files[0];

            files = Directory.GetFiles(ProjectDirectory, "AssemblyInfo.cs", SearchOption.AllDirectories);
            if (files != null && files.Length > 0)
                AssemblyInfoFileName = files[0];

            InitialisePackages();
            InitialiseProjectXmlProperties();
            InitialiseConfigurations();
        }

        void InitialisePackages()
        {
            string f = Path.Combine(ProjectDirectory, "packages.config");
            if (!File.Exists(f))
                return;

            PackagesFileName = f;
            XDocument xdoc = XDocument.Load(PackagesFileName);

            Packages = (from n in xdoc.Descendants()
                        where n.Name.LocalName == "packages"
                        from n2 in n.Descendants()
                        where n2.Name.LocalName == "package"
                        select new PackageInfo()
                        {
                             Id = n2.Attribute("id").Value,
                             Version = n2.Attribute("version").Value,
                             TargetFramework = n2.Attribute("targetFramework").Value
                        }).ToList();
        }

        void InitialiseProjectXmlProperties()
        {
            XDocument xdoc = XDocument.Load(FileName, LoadOptions.PreserveWhitespace);

            var defaultPropertyGroupNode = (from n in xdoc.Descendants()
                                            where n.Name.LocalName.Equals("Project", StringComparison.OrdinalIgnoreCase)
                                            from n2 in n.Descendants()
                                            where n2.Name.LocalName.Equals("PropertyGroup", StringComparison.OrdinalIgnoreCase) &&
                                                !n2.HasAttributes
                                            select n2
                                           ).FirstOrDefault();

            if (defaultPropertyGroupNode == null)
                throw new InvalidOperationException("Could not locate default PropertyGroup in project file.");

            var node = (from n in defaultPropertyGroupNode.Descendants()
                        where n.Name.LocalName.Equals("OutputType", StringComparison.OrdinalIgnoreCase)
                        select n).Single();
            OutputType = node.Value;

            node = (from n in defaultPropertyGroupNode.Descendants()
                        where n.Name.LocalName.Equals("AssemblyName", StringComparison.OrdinalIgnoreCase)
                        select n).Single();
            AssemblyName = node.Value;
        }

        void InitialiseConfigurations()
        {
            var result = new Dictionary<string, ConfigurationInfo>();
            XDocument xdoc = XDocument.Load(FileName);

            // Stupid namespaces...
            var nodes = (from n in xdoc.Descendants()
                        where n.Name.LocalName == "Project"
                        from n2 in n.Descendants()
                        where n2.Name.LocalName.StartsWith("PropertyGroup") &&
                              n2.HasAttributes      // Avoid the default
                         select new ConfigurationInfo(this)
                            {
                                ConfigurationAndPlatform = n2.FirstAttribute.Value,
                                OutputPath = (from p in n2.Descendants() where p.Name.LocalName == "OutputPath" select p.Value).SingleOrDefault()
                            }
                        ).ToList();

            foreach (var node in nodes)
            {
                int index = node.ConfigurationAndPlatform.IndexOf("==") + 2;
                node.ConfigurationAndPlatform = node.ConfigurationAndPlatform.Substring(index).Trim().Replace("'", "");

                string[] parts = node.ConfigurationAndPlatform.Split('|');
                node.Configuration = parts[0];
                node.Platform = parts[1];
                node.OutputPath = node.OutputPath.Trim().TrimEnd(new[] { '\\' });

                result[node.Configuration] = node;
            }

            Configurations = result;
        }

        /// <summary>
        /// Reads the version number from AssemblyVersion attribute in the AssemblyInfo.cs file.
        /// You can also set this property, which causes the file to be saved with the new number.
        /// </summary>
        public string VersionNumber
        {
            get
            {
                if (AssemblyInfoFileName == null)
                    return null;
                string code = File.ReadAllText(AssemblyInfoFileName);

                var match = Regex.Match(code, avPattern, RegexOptions.Multiline);
                if (match.Success && match.Groups.Count == 2)
                    return match.Groups[1].Value.Trim();
                else
                    return null;
            }
            set
            {
                if (String.IsNullOrWhiteSpace(value))
                    throw new ArgumentNullException("Cannot set VersionNumber to blank");
                if (AssemblyInfoFileName == null)
                    throw new InvalidOperationException("Cannot set VersionNumber because AssemblyInfoFileName is null.");

                string code = File.ReadAllText(AssemblyInfoFileName);
                string replacement = String.Format("[assembly: AssemblyVersion(\"{0}\")]", value);
                code = Regex.Replace(code, avPattern, replacement, RegexOptions.Multiline);
                replacement = String.Format("[assembly: AssemblyFileVersion(\"{0}\")]", value);
                code = Regex.Replace(code, afvPattern, replacement, RegexOptions.Multiline);
                File.WriteAllText(AssemblyInfoFileName, code);
            }
        }

        public string BinDirectory
        {
            get
            {
                string dir = Path.Combine(ProjectDirectory, "bin");
                if (Directory.Exists(dir))
                    return dir;
                else
                    return null;
            }
        }

        public string ObjDirectory
        {
            get
            {
                string dir = Path.Combine(ProjectDirectory, "obj");
                if (Directory.Exists(dir))
                    return dir;
                else
                    return null;
            }
        }

        public string OutputExtension
        {
            get
            {
                if (String.Equals(OutputType, "Exe", StringComparison.OrdinalIgnoreCase))
                    return "exe";
                else
                    return "dll";
            }
        }

        public string OutputFileName
        {
            get
            {
                return String.Format("{0}.{1}", AssemblyName, OutputExtension);
            }
        }

        /// <summary>
        /// Deep-cleans a project, which means to try and completely delete the bin and obj folders.
        /// It is safe to call this method even if the folders do not exist.
        /// Unfortunately, for EXEs only, if you call this while Visual Studio is open it is likely
        /// that you will be unable to delete the entire directory, because the *.vshost.exe file will be locked.
        /// You can disable that if you want, but it's probably not worth the effort.
        /// See "How to: Disable the Hosting Process" https://msdn.microsoft.com/en-us/library/ms185330.aspx
        /// </summary>
        public void DeepClean()
        {
            SafeDeleteDirectory(ObjDirectory);
            SafeDeleteDirectory(BinDirectory);
        }

        public int UpdateNuSpecDependencies()
        {
            if (String.IsNullOrWhiteSpace(NuSpecFileName))
                throw new InvalidOperationException("The NuSpecFileName is not set, cannot perform requested update.");
            if (String.IsNullOrWhiteSpace(PackagesFileName))
                throw new InvalidOperationException("The PackagesFileName is not set, cannot perform requested update.");

            XDocument xdoc = XDocument.Load(NuSpecFileName, LoadOptions.PreserveWhitespace);

            var nodes = (from n in xdoc.Descendants()
                           where n.Name.LocalName.Equals("metadata", StringComparison.OrdinalIgnoreCase)
                           from n2 in n.Descendants()
                           where n2.Name.LocalName.Equals("dependencies", StringComparison.OrdinalIgnoreCase)
                           select n2
                          ).ToList();

            if (nodes == null || nodes.Count() == 0)
                return 0;
            if (nodes.Count() > 1)
                throw new InvalidOperationException("Found more than 1 <dependencies> element. Check your nuspec file.");

            var dependencyNode = nodes[0];

            dependencyNode.RemoveNodes();
            
            foreach (var package in Packages.OrderBy(p => p.Id))
            {
                dependencyNode.Add(new XText(Environment.NewLine));
                dependencyNode.Add(new XText("      "));
                var elem = new XElement("dependency");
                elem.Add(new XAttribute("id", package.Id));
                elem.Add(new XAttribute("version", package.Version));
                dependencyNode.Add(elem);
            }

            dependencyNode.Add(new XText(Environment.NewLine));
            dependencyNode.Add(new XText("    "));

            // Save, preserving whitespace formatting (round trip).
            xdoc.Save(NuSpecFileName, SaveOptions.DisableFormatting);

            return Packages.Count();
        }

        /// <summary>
        /// Deletes a directory, but only if it exists. First turns off the read-only flag on
        /// all files, then tries to delete each file in turn. Then deletes the directory.
        /// The method will not throw, but may not be able to delete the directory if processes
        /// have locks on files.
        /// </summary>
        /// <param name="directory">The directory to delete.</param>
        /// <returns>True if the directory was deleted (or does not exist), false otherwise.</returns>
        public static bool SafeDeleteDirectory(string directory)
        {
            if (directory == null || !Directory.Exists(directory))
                return true;

            var di = new DirectoryInfo(directory);
            foreach (var fi in di.EnumerateFiles("*", SearchOption.AllDirectories))
            {
                try
                {
                    if (fi.IsReadOnly)
                        fi.IsReadOnly = false;
                    fi.Delete();
                }
                catch { }
            }

            try
            {
                Directory.Delete(directory, true);
            }
            catch { }
            
            bool didDelete = !Directory.Exists(directory);
            return didDelete;
        }
    }

"@

Add-Type -TypeDefinition $source -ReferencedAssemblies "System.Xml", "System.Xml.Linq"


<#
.SYNOPSIS
Searches for a file(s) occurring anywhere under the StartDirectory. 

.DESCRIPTION
This is a simple wrapper around Get-ChildItem. It can return more than 1 file.

.PARAMETER FileName
The filename to find. Wildcards acceptable.

.PARAMETER StartDirectory
The directory to start the search in. You may leave this null, in which case
the directory of the script will be tried, and if no files are found (which
is typical if you are running the script from its default installation in
the Solution\.nuget folder) it will then try the parent directory of the
script - this will typically be the folder containing the solution. If you
do not want this behaviour then specify an explicit start directory.

.OUTPUTS
List of filenames.

.EXAMPLE
$filename = Find-File "AssemblyInfo.cs" "C:\temp\Foo"

.INPUTS
A list of filenames to find. Wildcards acceptable.

.OUTPUTS
A list of FileInfo objects.

.EXAMPLE
This example finds all CSharp project files in the current solution and pipes
them to Get-Project to create Project objects for each one.

Find-File "*.csproj" | Get-Project

.EXAMPLE
This example shows how to pipe a list of file wildcards to Find-File.

"*.csproj", "Assemb*.cs" | Find-File | % { $_.FullName }
#>
function Find-File
{
    [CmdletBinding()]
    param(
	[Parameter(Position=0, Mandatory=$true, ValueFromPipeline=$true, ValueFromPipelineByPropertyName=$true)]
	[Alias("FullName")]
    [String[]]$FileName,
	[Parameter(Position=1, Mandatory=$false)] [String]$StartDirectory
    )

    Process
    {
        foreach ($fname in $FileName)
        {
            if ($StartDirectory)
            {
        	    Get-ChildItem -Path $StartDirectory -Recurse -Filter $fname
            }
            else
            {
        	    $StartDirectory = $PSScriptRoot
        	    $files = Get-ChildItem -Path $StartDirectory -Recurse -Filter $fname
        	    if ($files)
        	    {
            		Write-Output $files
            	}
        	    $StartDirectory = Split-Path -Parent $PSScriptRoot
        	    Get-ChildItem -Path $StartDirectory -Recurse -Filter $fname
            }
        }
    }
}

<#
.SYNOPSIS
Searches for MSBuild.exe and returns the path to it, if found, as a string.

.DESCRIPTION
First tries to find MSBuild for .Net 4, it that is unsuccessful it then
tries 3.5 and 2.0. The registry is checked to see where MSBuild.exe should
be located, and if it really is there the path to the exe is returned.
On a machine which does not have MSBuild installed nothing will be returned.

.EXAMPLE
$msBuildExe = Find-MSBuild
#>
function Find-MSBuild
{
    foreach ($dotNetVersion in @("4.0", "3.5", "2.0"))
    {
	    $regKey = "HKLM:\software\Microsoft\MSBuild\ToolsVersions\$dotNetVersion"
	    $regProperty = "MSBuildToolsPath"
	    $msbuild = Join-Path -path (Get-ItemProperty $regKey).$regProperty -childpath "msbuild.exe"
	    if (Test-Path $msbuild)
	    {
    		return $msbuild
    	}
    }
}

<#
.SYNOPSIS
Searches for NuGet.exe and returns the path to it, if found, as a string.
The folder containing this module has priority when looking for NuGet.exe.

.DESCRIPTION
If NuGet.exe exists in the same folder as the script then that file is returned,
otherwise we look for it in the PATH. If it is not on the path, if
DownloadIfNecessary is true, an attempt will be made to download NuGet.exe from
the Internet to this script's folder. If that succeeds the path to the downloaded
NuGet will be returned. If all the above checks fail, then nothing is returned.

.PARAMETER DownloadIfNecessary
If true, an attempt will be made to download NuGet.exe from the Internet. This
attempt will only be made if NuGet.exe cannot be located on the computer.

.EXAMPLE
This example finds NuGet if it is on this computer, but does not attempt to
download it if it is not.

$nuget = Find-NuGet


.EXAMPLE
This example attempts to find NuGet.exe, and downloads it if it is not found on
this computer.

$nuget = Find-NuGet -DownloadIfNecessary
#>
function Find-NuGet
{
	[CmdletBinding()]
	param(
	[Parameter(Position=0, Mandatory=$false)] [Switch]$DownloadIfNecessary
	)

    $nuget = Join-Path -path $PSScriptRoot -ChildPath "NuGet.exe"
    if (Test-Path $nuget)
    {
	    return $nuget
    }
    else
    {
	    $exists = Test-CommandExists "NuGet.exe"
	    if ($exists)
	    {
		    return "NuGet.exe"
	    }
		elseif ($DownloadIfNecessary)
		{
			Invoke-NuGetDownload $nuget
			if (Test-Path $nuget)
			{
				return $nuget
			}
		}

    }
}

<#
.SYNOPSIS
Finds a project. If found, returns the FileInfo for the project file. The Find-File
function is used to do the search.

.DESCRIPTION
A recursive search is made for the .csproj file, and if that is not found another
search is done for a .vbproj file. If that is not found then nothing is returned.

.PARAMETER ProjectName
The name of the project, for example "Foo.Core". The project file to be searched
for will then be Foo.Core.csproj, or Foo.Core.vbproj. (.csproj is searched for
first). Wildcards are acceptable, indeed "*" will find all projects in the solution.

.PARAMETER StartDirectory
The directory to start the search from. You can leave this null to search the script's
directory and the script's parent directory (see Find-File). It can also be a relative
path such as "../../Other/Dir".

.INPUTS
The name(s) of the project(s).

.OUTPUTS
A set of FileInfo objects for the projects that were found.

.EXAMPLE
$project = Find-Project "Foo.Core"
$project = Find-Project "Foo.Core" ".."               # same results as the above
$project = Find-Project "Foo.Core" "../../Somewhere"  # Search outside the solution dir

.EXAMPLE
This example shows Find-Project taking pipeline input and writing a set of FileInfos
to the pipeline, which are then built into Project objects by Get-Project.

"Demo*", "Foo*" | Find-Project | Get-Project

.EXAMPLE
This is the canonical example of finding all projects in a solution and constructing
Project objects for them.

Find-Project "*" | Get-Project
#>
function Find-Project
{ 
    [CmdletBinding()]
    param(
	[Parameter(Position=0, Mandatory=$true, ValueFromPipeline=$true)] [String[]]$ProjectName,
	[Parameter(Position=1, Mandatory=$false)] [String]$StartDirectory
    )

    Process
    {
    	if ($StartDirectory)
    	{
    		$StartDirectory = Resolve-Path $StartDirectory
    	}

    	foreach ($proj in $ProjectName)
    	{
    		$didFind = $false
    		foreach ($ext in "csproj", "vbproj")
    		{
    			$foundFile = Find-File "$proj.$ext" $StartDirectory
    			if ($foundFile)
    			{
    				Write-Output $foundFile
    				$didFind = $true
    			}
    		}

    		if (!$didFind)
    		{
    			Write-Error "Could not locate the project file for the name $proj"
    		}
    	}
    }
}

<#
.SYNOPSIS
Gets the version number from an assembly.

.DESCRIPTION
Retrieve the assembly version without loading the assembly. A naive version using
  $asm = [Reflection.Assembly]::LoadFile($exePath)
  $asm = [Reflection.Assembly]::ReflectionOnlyLoadFrom($exePath)
  $asmName = $asm.GetName()
will load the assembly into PowerShell's appdomain and keep it locked, meaning
that the script is not rerunnable. This version does not suffer from that problem.

.PARAMETER FileName
The filename of the assembly.

.EXAMPLE
$version = Get-AssemblyVersion "C:\temp\foo.dll"
#>
function Get-AssemblyVersion
{
    [CmdletBinding()]
    param(
	[Parameter(Position=0, Mandatory=$true)] [String]$FileName
    )

    $version = [System.Reflection.AssemblyName]::GetAssemblyName($filename).Version;
    return $version
}

<#
.SYNOPSIS
Returns the complete set of arguments to be used when invoking MSBuild for a clean or build task.

.DESCRIPTION
Returns an array of arguments to be used to invoke MS Build. You must specify at least one
of $Clean or $Build. It is not normally necessary to use this function in your scripts, because
it is called by Invoke-MSBuild or Invoke-MSClean.

.PARAMETER Project
Project object, from Get-Project.

.PARAMETER Clean
If true, includes the Clean target in the build arguments.

.PARAMETER Build
If true, includes the Build target in the build arguments.

.PARAMETER Verbosity
MSBuild verbosity flag.

.PARAMETER Configuration
The MSBuild Configuration to build, for example "Release".

.PARAMETER Platform
The Platform to build, for example "AnyCPU".

.EXAMPLE
$project = Get-Project "C:\temp\Foo.csproj"
$args = Get-MSBuildArguments $project $true $false "normal"     # Args for a chatty clean.
#>
function Get-MSBuildArguments
{
    [CmdletBinding()]
    param(
	[Parameter(Position=0, Mandatory=$true)] [Project]$Project,
	[Parameter(Position=1, Mandatory=$false)] [Bool]$Clean = $true,
	[Parameter(Position=2, Mandatory=$false)] [Bool]$Build = $true,
	[Parameter(Position=3, Mandatory=$false)] [String]$Verbosity = "minimal",
	[Parameter(Position=4, Mandatory=$false)] [String]$Configuration = "Release",
	[Parameter(Position=5, Mandatory=$false)] [String]$Platform = "AnyCPU"
    )

    $Targets = ""
    if ($Clean)
    {
    	$Targets = "Clean"
    }
    if ($Build)
    {
    	if ($Targets)
    	{
    		$Targets += ";"
    	}
    	$Targets += "Build"
    }

    if (!$Targets)
    {
    	Write-Error "Must specify either $Clean, $Build or both"
    }

    $args = @(
    	$($Project.FileName),
    	"/target:$Targets",
    	"/nologo",
    	"/verbosity:$Verbosity",
    	"/p:Configuration=$Configuration",
    	"/p:RunCodeAnalysis=False"
    )

    if ($Platform)
    {
    	$args += "/p:PlatformTarget=$Platform"
    }

    return $args
}

<#
.SYNOPSIS
Given a project file ("Foo.csproj"), creates an instance of the Project class and returns it.
The object contains much useful information about the Visual Studio project.

.DESCRIPTION
This is the method to use to get a Project instance. Once you have the instance many more
methods become available. Some are methods on the object itself, some are PowerShell functions
into which you should pass the object.

.PARAMETER FileName
The project file to load.

.INPUTS
An array of project filenames. The full path to the project file is required.

.OUTPUTS
An array of Project objects.

.EXAMPLE
$project = Get-Project "C:\temp\Foo.csproj"

.EXAMPLE
This finds all projects in the solution and creates Project objects for them.

Find-Project "*" | Get-Project
#>
function Get-Project
{
    [CmdletBinding()]
    param(
	[Parameter(Position=0, Mandatory=$true, ValueFromPipeline=$true, ValueFromPipelineByPropertyName=$true)]
	[Alias("FullName")]
	[String[]]$FileName
    )

    Process
    {
    	foreach ($fn in $FileName)
    	{
    		if (Test-Path $fn)
    		{
    			$projectObject = New-Object -type Project -ArgumentList $fn
    			Write-Output $projectObject
    		}
    		else
    		{
    			Write-Error "The project file $fn does not exist."
    		}
    	}
    }
}

<#
.SYNOPSIS
Deletes the bin and obj directories under a project.

.DESCRIPTION
Deletes the bin and obj directories under a project. It is safe to call this function
even if the directories do not exist. It is possible that the directories will not
actually be deleted if another process has file locks open on a file that resides
in the directories; in that case a warning is printed.

.PARAMETER Project
Project object, from Get-Project.

.INPUTS
The Project object to clean (can be pipelined).

.OUTPUTS
The Project object that was passed in.

.EXAMPLE
$project = Get-Project "C:\temp\Foo.csproj"
Invoke-DeepClean $project

.EXAMPLE
This example shows how to deep-clean all projects in the solution.

Find-Project "*" | Get-Project | Invoke-DeepClean > $null
#>
function Invoke-DeepClean
{
    [CmdletBinding()]
    param(
	[Parameter(Position=0, Mandatory=$true, ValueFromPipeline=$true)] [Project[]] $Project
    )

    Process
    {
        foreach ($proj in $Project)
        {
			foreach ($dir in $proj.ObjDirectory, $proj.BinDirectory)
			{
				if ($dir)
				{
					if (Test-Path $dir)
					{
						$didDelete = [Project]::SafeDeleteDirectory($dir)
						if ($didDelete)
						{
							Write-Host "Deleted $dir"
						}
						else
						{
							Write-Warning "Could not completely delete $dir, some files remain"
						}
					}
				}
			}

			Write-Output $proj
        }
    }
}

<#
.SYNOPSIS
Deep-cleans the packages folder by removing downloaded package directories.

.DESCRIPTION
This function does not alter the repositories.config file, it just deletes the downloaded
packages. This can be useful to force nuget to redownload a package.

.PARAMETER DirectoryPattern
Pattern to match directories in the packages directory.

.PARAMETER DoIt
You must specify this switch in order for the delete to actually occur. If not specified,
the function will print what it would delete but will not actually delete the directories.

.PARAMETER PackageDirectory
The path of the package directory. This can be left blank to have it automatically
determined (which is done by searching for the repositories.config file).

.EXAMPLE
Invoke-DeepCleanPackages "NewtonSoft*.*"
Invoke-DeepCleanPackages "*.*"
#>
function Invoke-DeepCleanPackages
{
	[CmdletBinding()]
	param(
	[Parameter(Position=0, Mandatory=$true)] [String]$DirectoryPattern,
	[Parameter(Position=1, Mandatory=$false)] [Switch]$DoIt,
	[Parameter(Position=2, Mandatory=$false)] [String]$PackageDirectory
	)

	if (!$PackageDirectory)
	{
		$repFile = Find-File "repositories.config"
		if (!$repFile)
		{
			Write-Error "Could not locate repositories.config file (which determines the location of the packages folder)."
			return
		}
		else
		{
			Write-Host "Found repo file at $($repFile.FullName)"
		}
		$PackageDirectory = Split-Path -Parent $repFile.FullName
	}

	if (!(Test-Path $PackageDirectory))
	{
		Write-Error "The package directory $PackageDirectory does not exist."
		return
	}

	Write-Host "Found package directory at $PackageDirectory"
	$dirs = Get-ChildItem -Path $PackageDirectory -Attributes Directory -Filter $DirectoryPattern
	if (!$dirs)
	{
		Write-Host "No package directories match your pattern of $DirectoryPattern"
		return
	}

	foreach ($dir in $dirs)
	{
		if ($DoIt)
		{
			Write-Host "Deleting $($dir.FullName)"
			Remove-Directory $dir.FullName
		}
		else
		{
			Write-Host "WOULD DELETE $($dir.FullName)"
		}
	}
}

<#
.SYNOPSIS
Runs MSBuild with the "Build" target.

.DESCRIPTION
Runs MSBuild to do a Build. If you are doing a build in order to build a NuGet package,
it is recommended you call Invoke-MSClean or even better, Invoke-DeepClean, first. This
will ensure that any leftover garbage is removed.

.PARAMETER Project
Project object, from Get-Project.

.PARAMETER Verbosity
MS Build verbosity flag.

.PARAMETER Configuration
The Configuration to build, for example "Release".

.PARAMETER Configuration
The Platform to build, for example "AnyCPU".

.INPUTS
An array of Project objects.

.OUTPUTS
The same array of Project objects that was passed in.

.EXAMPLE
$project = Get-Project "C:\temp\Foo.csproj"
Invoke-MSBuild $project

.EXAMPLE
This example shows how to build all projects in the solution in Debug mode (Release
is the default).

Find-Project "*" | Get-Project | Invoke-MSBuild -Configuration Debug > $null

.EXAMPLE
This example shows how to build all projects in the solution in multiple configurations, such
as when building multiple framework versions.

Find-Project "*" | Get-Project | % { $project = $_ ; "Release40","Release45" |  % { Invoke-MSBuild $project -Configuration $_ }} > $null
#>
function Invoke-MSBuild
{
    [CmdletBinding()]
    param(
    [Parameter(Position=0, Mandatory=$true, ValueFromPipeline=$true)] [Project[]]$Project,
    [Parameter(Position=1, Mandatory=$false)] [String]$Verbosity = "minimal",
    [Parameter(Position=2, Mandatory=$false)] [String]$Configuration = "Release",
    [Parameter(Position=3, Mandatory=$false)] [String]$Platform = "AnyCPU"
    )

    Begin
    {
	    $msbuild = Find-MSBuild
    }
    Process
    {
    	foreach ($proj in $Project)
    	{
    		$filename = $proj.FileName
    		$args = Get-MSBuildArguments $filename $false $true $Verbosity $Configuration $Platform

    		Write-Host "MSBuild.exe $args"
    		&$msbuild $args | Write-Host # Pipe ensures the pipeline is not polluted with MSBuild's output.

    		if ($lastExitCode -ne 0)
    		{
    			Write-Error "Error while running MSBuild for $filename"
    		}

    		Write-Host "Building $filename complete"
    		Write-Output $proj
    	}
    }
}

<#
.SYNOPSIS
Runs MSBuild with the Clean target.

.DESCRIPTION
Runs MSBuild to do a Clean. This is equivalent to doing a "Clean" in Visual Studio.
As in Visual Studio, this does not necessarily remove everything in the bin folder -
it only removes things that are in MSBuild's "output file list". Stray files may
get included when packaging. To avoid this, it is recommended to use the related
function Invoke-DeepClean which simply deletes the bin and obj folders, thus forcing
a complete rebuild from a known-clean situation.

.PARAMETER Project
Project object, from Get-Project.

.PARAMETER Verbosity
MS Build verbosity flag.

.PARAMETER Configuration
The Configuration to build, for example "Release".

.INPUTS
An array of Project objects.

.OUTPUTS
The same array of Project objects that was passed in.

.EXAMPLE
$project = Get-Project "C:\temp\Foo.csproj"
Invoke-MSClean $project

.EXAMPLE
This example shows how to clean all projects in the solution.

Find-Project "*" | Get-Project | Invoke-MSClean > $null
#>
function Invoke-MSClean
{
    [CmdletBinding()]
    param(
	[Parameter(Position=0, Mandatory=$true, ValueFromPipeline=$true)] [Project[]]$Project,
	[Parameter(Position=1, Mandatory=$false)] [String]$Verbosity = "minimal",
	[Parameter(Position=2, Mandatory=$false)] [String]$Configuration = "Release"
    )

    Begin
    {
    	$msbuild = Find-MSBuild
    }
    Process
    {
    	foreach ($proj in $Project)
    	{
    		$filename = $proj.FileName
    		$args = Get-MSBuildArguments $filename $true $false $Verbosity $Configuration $Platform
    		Write-Host "MSBuild.exe $args"
    		&$msbuild $args | Write-Host

    		if ($lastExitCode -ne 0)
    		{
    			Write-Error "Error while running MSBuild for clean for $filename"
    		}

    		Write-Host "Cleaning $filename complete"
    		Write-Output $proj
    	}
    }
}


<#
.SYNOPSIS
Downloads the latest version of NuGet.exe from the Internet.

.DESCRIPTION
The latest version of NuGet is downloaded from http://NuGet.org/NuGet.exe
and written to the specified filename. If the file already exists it will be
overwritten.

.PARAMETER DestinationFilename
The filename (full path is best) to which the downloaded NuGet.exe will be saved.
If not specified, NuGet.exe is placed in the same directory as the script.

.EXAMPLE
Invoke-NuGetDownload     # Places NuGet.exe into the folder of this script.

.EXAMPLE
Invoke-NuGetDownload "C:\temp\NuGet.exe"
#>
function Invoke-NuGetDownload
{
	[CmdletBinding()]
	param(
	[Parameter(Position=0, Mandatory=$false)] [String]$DestinationFilename = (Join-Path -Path $PSScriptRoot -ChildPath "NuGet.exe")
	)

	$sourceNuGetExe = "http://NuGet.org/NuGet.exe"
	Write-Host "Downloading $sourceNuGetExe to $DestinationFilename, please wait..."
	Invoke-WebRequest $sourceNuGetExe -OutFile $DestinationFilename
	Write-Host "Download NuGet.exe complete."
}

<#
.SYNOPSIS
Runs "NuGet Pack" on a project. If successful, sets the NuPkgFileName property on the
Project object to aid with pipelining to Invoke-NuGetPush.

.DESCRIPTION
Given a project object (from Get-Project) this function attempts to run 'NuGet pack' on the
project. The project must have been previously built (it is recommended to do a DeepClean
first), and must have a nuspec file. You may specify an explicit version number for the
NuGet package (this is NOT the version number of the built assembly) or set it automatically
based on the AssemblyInfo.cs or the built assembly (see full help for details).

.PARAMETER Project
Project object, from Get-Project.

.PARAMETER Version
Version number of the nupkg, e.g. "1.2.3.0". Alternatively, you may specify "asm" to
try and retrieve the version number from a built assembly, or "info" to retrieve the
version number from the AssemblyInfo.cs file. Finally, if you leave the version number
blank the version number specified in the nuspec file will be used.

.PARAMETER OutputDirectory
Where to place the nupkg file.

.PARAMETER Verbosity
NuGet verbosity level (quiet, normal, detailed).

.PARAMETER NonInteractive
Do not prompt for user input or confirmations.

.PARAMETER Properties
An array of additional properties to pass to NuGet Pack. These properties can be used for
textual substitution in the nuspec file. Note that these properties are completely
independent of MSBuild variables. So if you are using '$configuration$' in your nuspec
file, you must specify it in this array.

.INPUTS
An array of Project objects.

.OUTPUTS
The same array of Project objects that was passed in.

.EXAMPLE
This example shows how to specify that the version number for the nupkg should be retrieved
from AssemblyInfo.cs, and how to specify properties that NuGet will substitute in the
nuspec file.

$project = Get-Project "C:\temp\Foo.csproj"
Invoke-NuGetPack $project -Version info -Properties @("Configuration=Release", "Key=Value")

.EXAMPLE
This example shows how to build and pack all projects in a solution, using
version numbers taken from the built assemblies.
Find-Project "*" | Get-Project | Invoke-MSBuild | Invoke-NuGetPack -Version asm > $null
#>
function Invoke-NuGetPack
{
	[CmdletBinding()]
	param(
	[Parameter(Position=0, Mandatory=$true, ValueFromPipeline=$true)] [Project[]]$Project,
	[Parameter(Position=1, Mandatory=$false)] [String]$Version,
	[Parameter(Position=2, Mandatory=$false)] [String]$OutputDirectory,
	[Parameter(Position=3, Mandatory=$false)] [String]$Verbosity = "normal",
	[Parameter(Position=4, Mandatory=$false)] [Switch]$NonInteractive = $true,
	[Parameter(Position=5, Mandatory=$false)] [String[]]$Properties
	)

	Begin
	{
		$nuget = Find-NuGet -DownloadIfNecessary
	}
	Process
	{
		foreach ($proj in $Project)
		{
			Write-Host "Procesing $($proj.FileName)"
			$ver = $null

			if (!$proj.NuSpecFileName)
			{
				Write-Warning "The Project $($proj.Name) does not have a NuSpecFileName set, ignoring."
				continue
			}

			if (!(Test-Path $proj.NuSpecFileName))
			{
				Write-Warning "The nuspec file $($proj.NuSpecFileName) does not exist, ignoring."
				continue
			}

			$v = $null
			if ($Version -eq "asm")
			{
				Write-Host "Version is 'asm', so looking for a built assembly to get the version number from."
				Write-Warning "This can go wrong, it may pick up an old assembly, so it is a good idea to do a DeepClean first if you want to use this feature."

				foreach ($cfg in $proj.Configurations.GetEnumerator())
				{
					Write-Host "Searching for an assembly built with the $($cfg.Value.Configuration) configuration..."
					$asmFileName = $cfg.Value.FullOutputPath
					if (Test-Path $asmFileName)
					{
						$v = Get-AssemblyVersion $asmFileName
						Write-Host "Got version $v from $asmFileName."
						break
					}
				}
				if (!$v)
				{
					Write-Warning "Could not locate a built assembly, so the version number will be taken from the nuspec file."
				}
			}
			elseif ($Version -eq "info")
			{
				$v = $proj.VersionNumber;
				if (!$v)
				{
					Write-Warning "Could not retrieve the Version from your AssemblyInfo.cs, so the version number will be taken from the nuspec file."
				}
				else
				{
					Write-Warning "Using version $v from your AssemblyInfo.cs. You should ensure that all assemblies you are packing were rebuilt with this version number."
				}
			}
			elseif (!$Version)
			{
				Write-Host "Version is not set, so the version number in the nuspec file will be used. Use 'asm' or 'info' to grab the version number from a built assembly or AssemblyInfo.cs"
			}
			else
			{
				$v = $Version
				Write-Host "Using your specified version of $v"
			}


			$args = @("pack", $proj.NuSpecFileName)

			if ($Verbosity)
			{
				$args += "-Verbosity", $Verbosity
			}

			if ($v)
			{
				$args += "-Version", $v
			}
			if ($OutputDirectory)
			{
				$args += "-OutputDirectory", $OutputDirectory
			}
			if ($NonInteractive)
			{
				$args += "-NonInteractive"
			}
			if ($Properties)
			{
				$args += "-Properties"
				$args += $Properties
			}

			Write-Host "NuGet.exe $args"
			$results = &$nuget $args    # $results is an array of strings.
			$results | Write-Host

			if ($LastExitCode -ne 0)
			{
				Write-Error "Error while running NuGet pack."
			}
			else
			{
				foreach ($line in $results)
				{
					$doesMatch = $line -match ".*Successfully.*?'(.*?)'"
					if ($doesMatch)
					{
						$proj.NuPkgFileName = $Matches[1]
						Write-Host "Package was created. Project.NuPkgFileName is now $($proj.NuPkgFileName)"
					}
				}
			}

			Write-Host "NuGet pack for $($proj.Name) completed"
			Write-Output $proj
		}
	}
}

<#
.SYNOPSIS
Pushes a nuget package to the specified feed.

.DESCRIPTION
Specify the full path of the filename to push, and the feed to push it to.

.PARAMETER Project
Project object. If the NuPkgFileName property is set to a file that exists, that
file will be pushed. Can be pipelined.

.PARAMETER NuPkgFileName
Full path of the nupkg file to push. Can be pipelined.

.PARAMETER NuGetFeed
The feed to push to. Defaults to 'LocalNuGetFeed' to avoid accidentally pushing things
to the official packaging respository. To push to the offical repository, use
'http://nuget.org'. To push to the staging repository, use 'http://staging.nuget.org'.

.PARAMETER Verbosity
NuGet verbosity level (quiet, normal, detailed).

.PARAMETER NonInteractive
Do not prompt for user input or confirmations.

.INPUTS
A pipeline of Project objects, or alternatively FileInfo objects representing
nupkg filenames.

.OUTPUTS
An array of the filenames that were pushed.

.EXAMPLE
Invoke-NuGetPush "C:\temp\foo.1.0.0.0.pkg" "http://nuget.org"

.EXAMPLE
This example shows how to pack and push an entire solution to the default "LocalNuGetFeed".

Find-Project "*" | Get-Project | Invoke-MSBuild | Invoke-NuGetPack -Version 9.8.7 -Properties "Configuration=Release" | Invoke-NuGetPush
#>
function Invoke-NuGetPush
{
	[CmdletBinding()]
	param(
	[Parameter(Position=0, Mandatory=$false, ValueFromPipeline=$true)] [Project[]]$Project,
	[Parameter(Position=1, Mandatory=$false, ValueFromPipelineByPropertyName=$true)]
	[Alias("FullName")]
	[String[]]$NuPkgFileName,
	[Parameter(Position=2, Mandatory=$false)] [String]$NuGetFeed = "LocalNuGetFeed",
	[Parameter(Position=3, Mandatory=$false)] [String]$Verbosity = "normal",
	[Parameter(Position=4, Mandatory=$false)] [Switch]$NonInteractive = $true
	)

	Begin
	{
		$nuget = Find-NuGet -DownloadIfNecessary
	}
	Process
	{
		$filesToPush = $NuPkgFileName
		foreach ($proj in $Project)
		{
			$filesToPush += $proj.NuPkgFileName
		}

		$filesToPush = $filesToPush | Select -Unique

		foreach ($filename in $filesToPush)
		{
			if (!(Test-Path $filename))
			{
				Write-Error "The nupkg file $filename does not exist, ignoring."
				continue
			}

			$args = @("push", "$filename", "-Verbosity", $Verbosity)
			if ($NuGetFeed)
			{
				$args += "-Source", $NuGetFeed
			}
			if ($NonInteractive)
			{
				$args += "-NonInteractive"
			}

			Write-Host "NuGet.exe $args"
			&$nuget $args | Write-Host

			if ($LastExitCode -ne 0)
			{
				Write-Error "Error while running NuGet push for $filename"
				continue
			}
			else
			{
				Write-Output $filename
			}

			Write-Host "NuGet push to $NuGetFeed for $filename completed."
		}
	}
}

<#
.SYNOPSIS
Run NuGet package restore on a solution. (NuGet v2.7 or better required).

.DESCRIPTION
Run NuGet package restore on a solution.

.PARAMETER SolutionFile
The solution file to restore packages for.

.PARAMETER Source
NuGet source to restore from. Examples are "LocalNuGetFeed", "nuget.org" and
"https://staging.nuget.org/api/v2".

.PARAMETER Verbosity
NuGet verbosity level (quiet, normal, detailed).

.PARAMETER NonInteractive
Do not prompt for user input or confirmations.

.INPUTS
A pipeline of strings or FileInfos specifying solution files.

.EXAMPLE
Invoke-NuGetRestore "C:\temp\MySolutionDir\MyStuff.sln"
Invoke-NuGetRestore $solutionFile -Verbosity "detailed"

.EXAMPLE
This example shows how to run a restore for all solutions that can be found
by Find-File (typically this will be 1 solution, but this form can be used
to create scripts that are independent of the solution name).

Find-File "*.sln" | Invoke-NuGetRestore
#>
function Invoke-NuGetRestore
{
	[CmdletBinding()]
	param(
	[Parameter(Position=0, Mandatory=$true, ValueFromPipeline=$true, ValueFromPipelineByPropertyName=$true)]
	[Alias("FullName")]
	[String[]]$SolutionFile,
	[Parameter(Position=1, Mandatory=$false)] [String]$Source = "http://nuget.org",
	[Parameter(Position=2, Mandatory=$false)] [String]$Verbosity = "normal",
	[Parameter(Position=3, Mandatory=$false)] [Switch]$NonInteractive = $true
	)

	Begin
	{
		$nuget = Find-NuGet -DownloadIfNecessary
	}
	Process
	{
		foreach ($sln in $SolutionFile)
		{
			if (!(Test-Path $sln))
			{
				Write-Error "The solution file $sln does not exist, ignoring"
				continue
			}

			$args = @("restore", "$sln", "-Source", $Source, "-Verbosity", $Verbosity)
			if ($NonInteractive)
			{
				$args += "-NonInteractive"
			}

			Write-Host "NuGet.exe $args"
			&$nuget $args | Write-Host
			if ($LastExitCode -ne 0)
			{
				Write-Error "Error while running NuGet restore on sln"
			}
			else
			{
				Write-Host "NuGet restore for $sln completed."
			}
		}
	}
}

<#
.SYNOPSIS
Deletes a directory and all its contents, recursively. It is safe to call this function
on a directory that does not exist.

.DESCRIPTION
Unbelievably, the -Recurse flag to Remove-Item is broken, so we need this workaround
function to do it reliably.

.PARAMETER Directory
The directory to delete.

.INPUTS
Pipeline of strings or FileInfos naming the directories to be deleted.

.EXAMPLE
Remove-Directory "C:\temp\foo"
#>
function Remove-Directory
{
	[CmdletBinding()]
	param(
	[Parameter(Position=0, Mandatory=$true, ValueFromPipeline=$true, ValueFromPipelineByPropertyName=$true)]
	[Alias("FullName")]
	[String[]]$Directory
	)

	Process
	{
		foreach ($dir in $Directory)
		{
			if (Test-Path $dir)
			{
				Get-ChildItem -Path $dir -Recurse | Remove-Item -Force -Recurse
				Remove-Item $dir -Force
			}
		}
	}
}

<#
.SYNOPSIS
Returns $true if a command exists, $false otherwise.

.DESCRIPTION
The command may be a PowerShell built in, or an exe such as "nuget.exe".
This is better than the default Get-Command built-in because it will not
throw an exception if the command does not exist.

.PARAMETER Command
The command to check for existence.

.EXAMPLE
Test-CommandExists "nuget.exe"

.EXAMPLE
Test-CommandExists Get-Help
#>
function Test-CommandExists
{
	[CmdletBinding()]
	param(
	[Parameter(Position=0, Mandatory=$true)] $Command
	)

	$oldPreference = $ErrorActionPreference
	$ErrorActionPreference = 'stop'

	try
	{
		if (Get-Command $Command)
		{
			return $true
		}
	}
	catch
	{
		return $false
	}
	finally
	{
		$ErrorActionPreference = $oldPreference
	}
}

<#
.SYNOPSIS
Update the <dependencies> tag in a project's nuspec file.

.DESCRIPTION
If a project's nuspec file has a dependencies element, this method scans the project's
packages.config file and adds each entry to the nuspec file. In other words, the
packages that your package depends on are added to the dependencies element. The
dependencies element is completely rewritten by this method.

If the nuspec does not have a dependencies element then no action is taken, so to get
this method to work the minimum you have to do is add a blank <dependencies> tag.

This method writes an updated nuspec file to disk. The dependencies are sorted
alphabetically in order to try and reduce version control system churn.

.PARAMETER Project
The project.

.INPUTS
A pipeline of Project objects.

.OUTPUTS
The same Project objects that were sent in.

.EXAMPLE
$project = Get-Project "C:\temp\Foo.csproj"
Update-PackageDependencies $project
#>
function Update-NuSpecDependencies
{
	[CmdletBinding()]
	param(
	[Parameter(Position=0, Mandatory=$true, ValueFromPipeline=$true)] [Project[]]$Project
	)

	Process
	{
		foreach ($proj in $Project)
		{
			if ($proj.PackagesFileName)
			{
				if (Test-Path $proj.PackagesFileName)
				{
					$numDependencies = $proj.UpdateNuSpecDependencies()
					Write-Host "Updated $($proj.PackagesFileName) with $numDependencies dependencies"
				}
				else
				{
					Write-Error "The nuspec filename $($proj.PackagesFileName) does not exist, ignoring."
				}
			}
			Write-Output $proj
		}
	}
}






# Fundamental functions, they do not use Project objects.
Export-ModuleMember -Function Find-File                    # PF = pipeline-friendly
Export-ModuleMember -Function Find-MSBuild                 #
Export-ModuleMember -Function Find-NuGet                   #
Export-ModuleMember -Function Get-AssemblyVersion          #
Export-ModuleMember -Function Get-MSBuildArguments         #
Export-ModuleMember -Function Invoke-DeepCleanPackages     #
Export-ModuleMember -Function Invoke-NuGetDownload         #
Export-ModuleMember -Function Remove-Directory             #
Export-ModuleMember -Function Test-CommandExists           #

# Project-related functions.
Export-ModuleMember -Function Find-Project                 # PF
Export-ModuleMember -Function Get-Project                  # PF
Export-ModuleMember -Function Invoke-DeepClean             # PF
Export-ModuleMember -Function Invoke-MSBuild               # PF
Export-ModuleMember -Function Invoke-MSClean               # PF
Export-ModuleMember -Function Invoke-NuGetPack             # PF
Export-ModuleMember -Function Invoke-NuGetPush             # PF
Export-ModuleMember -Function Invoke-NuGetRestore          # PF
Export-ModuleMember -Function Update-NuSpecDependencies    # PF
