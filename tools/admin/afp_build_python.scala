package afp


import isabelle._


object AFP_Build_Python {
  val default_version = "3.10.4"
  val default_mirror = "https://github.com/indygreg/python-build-standalone/releases/download/20220528"
  val default_license_mirror = "https://raw.githubusercontent.com/indygreg/python-build-standalone/20220528"

  def make_component_name(version: String): String = "python-" + version

  def make_archive_name(
    release: String,
    version: String,
    platform: Platform.Family.Value
  ): String = {
    val arch = platform match {
      case isabelle.Platform.Family.linux_arm => "aarch64-unknown-linux-gnu"
      case isabelle.Platform.Family.linux => "x86_64-unknown-linux-gnu"
      case isabelle.Platform.Family.macos => "x86_64-apple-darwin"
      case isabelle.Platform.Family.windows => "x86_64-windows-msvc-shared"
    }
    "cpython-" + version + "+" + release + "-" + arch + "-install_only.tar.gz"
  }


  /* build python environment */

  def build_python(
    requirements_file: Path,
    progress: Progress = new Progress,
    version: String = default_version,
    mirror: String = default_mirror,
    license_mirror: String = default_license_mirror,
    target_dir: Path = Path.current,
    verbose: Boolean = false
  ): Unit = {
    Isabelle_System.with_tmp_dir("python") { tmp_dir =>
      /* component */

      val component = make_component_name(version)
      val component_dir = Isabelle_System.new_directory(target_dir.absolute + Path.basic(component))
      progress.echo("Component " + component_dir)

      Isabelle_System.make_directory(component_dir)


      /* platform */

      val platform_name =
        proper_string(Isabelle_System.getenv("ISABELLE_PLATFORM64")) getOrElse
          error("No 64bit platform")

      val platform_dir = Isabelle_System.make_directory(component_dir + Path.basic(platform_name))


      /* archive */

      val Release = """^.*?([^/]+)$""".r

      val release =
        mirror match {
          case Release(release) => release
          case _ => error("Failed to determine release version from " + quote(mirror))
        }

      val platform = Platform.Family.values.find(Platform.Family.standard(_) == platform_name).get

      val archive_name =
        make_archive_name(release = release, version = version, platform = platform)

      /* download */

      val license_path = tmp_dir + Path.basic("LICENSE")
      val license_download_url = license_mirror + "/LICENSE.cpython.txt"
      Isabelle_System.download_file(license_download_url, license_path)

      val archive_path = tmp_dir + Path.basic(archive_name)
      val download_url = mirror + "/" + archive_name
      Isabelle_System.download_file(download_url, archive_path, progress = progress)

      Isabelle_System.bash("tar xzf " + File.bash_path(archive_path), cwd = tmp_dir.file).check

      /* install */

      Isabelle_System.copy_dir(tmp_dir + Path.make(List("python", "bin")), platform_dir)
      Isabelle_System.copy_dir(tmp_dir + Path.make(List("python", "include")), platform_dir)
      Isabelle_System.copy_dir(tmp_dir + Path.make(List("python", "lib")), platform_dir)
      Isabelle_System.copy_dir(tmp_dir + Path.make(List("python", "share")), platform_dir)
      Isabelle_System.copy_file(license_path, component_dir)

      progress.echo("Installing additional packages")

      Isabelle_System.bash("bin/python3 -m pip install -r " + requirements_file,
        cwd = platform_dir.file,
        progress_stdout = progress.echo_if(verbose, _),
        progress_stderr = progress.echo_if(verbose, _)
      ).check


      /* settings */

      val etc_dir = Isabelle_System.make_directory(component_dir + Path.basic("etc"))
      File.write(etc_dir + Path.basic("settings"),
        """# -*- shell-script -*- :mode=shellscript:

ISABELLE_PYTHON="$COMPONENT/$ISABELLE_PLATFORM64"
""")


      /* README */

      File.write(component_dir + Path.basic("README"),
      "This Isabelle component provides a Python " + version +
        """ environment built from sources (""" + mirror + """)

AFP packages are installed.

        Fabian
        """ + Date.Format.date(Date.now()) + "\n")
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool = Isabelle_Tool("afp_build_python", "build afp python environment",
    Scala_Project.here,
  { args =>
    var target_dir = Path.current
    var license_mirror = default_license_mirror
    var requirements_file = Path.explode("$AFP_BASE/admin/sitegen-req.txt")
    var mirror = default_mirror
    var version = default_version
    var verbose = false

    val getopts = Getopts("""
Usage: isabelle afp_build_python [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -L URL       license URL
                 (default """" + default_license_mirror + """")
    -R FILE      requirements file (default "$AFP_BASE/admin/sitegen-req.txt")
    -U URL       download URL
                 (default """" + default_mirror + """")
    -V VERSION   version
                 (default: """" + default_version + """")
    -v           verbose

  Build python component with virtual environment.
""",
      "D:" -> (arg => target_dir = Path.explode(arg)),
      "L:" -> (arg => license_mirror = arg),
      "R:" -> (arg => requirements_file = Path.explode(arg)),
      "U:" -> (arg => mirror = arg),
      "V:" -> (arg => version = arg),
      "v" -> (_ => verbose = true))

    getopts(args)

    val progress = new Console_Progress()

    build_python(requirements_file, progress, version, mirror, license_mirror, target_dir, verbose)
  })
}