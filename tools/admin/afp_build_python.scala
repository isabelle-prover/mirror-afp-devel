package afp


import isabelle._


object AFP_Build_Python {
  val default_mirror = "https://www.python.org/ftp/python/3.9.8/Python-3.9.8.tgz"

  def make_component_name(version: String): String = "python-" + version


  /* build python environment */

  def build_python(
    requirements_file: Path,
    progress: Progress = new Progress,
    mirror: String = default_mirror,
    target_dir: Path = Path.current,
    verbose: Boolean = false
  ): Unit = {
    Isabelle_System.with_tmp_dir("python") { tmp_dir =>
      /* component */

      val Archive_Name = """^.*?([^/]+)$""".r
      val Version = """^Python-([0-9.]+)\.tgz$""".r

      val archive_name =
        mirror match {
          case Archive_Name(name) => name
          case _ => error("Failed to determine source archive name from " + quote(mirror))
        }

      val version =
        archive_name match {
          case Version(version) => version
          case _ => error("Failed to determine component version from " + quote(archive_name))
        }

      val component = make_component_name(version)
      val component_dir = Isabelle_System.new_directory(target_dir.absolute + Path.basic(component))
      progress.echo("Component " + component_dir)

      Isabelle_System.make_directory(component_dir)


      /* platform */

      val platform_name =
        proper_string(Isabelle_System.getenv("ISABELLE_PLATFORM64")) getOrElse
          error("No 64bit platform")

      val platform_dir = Isabelle_System.make_directory(component_dir + Path.basic(platform_name))


      /* download python */

      val archive_path = tmp_dir + Path.basic(archive_name)
      Isabelle_System.download_file(mirror, archive_path, progress = progress)

      Isabelle_System.bash("tar xzf " + File.bash_path(archive_path), cwd = tmp_dir.file).check
      val source_name = File.get_dir(tmp_dir)

      Isabelle_System.bash(
        "tar xzf " + archive_path + " && mv " + Bash.string(source_name) + " src",
        cwd = component_dir.file).check


      /* build */

      progress.echo("Building python for " + platform_name + " ...")

      val build_options = "--prefix=" + quote(platform_dir.toString) + " --enable-loadable-sqlite-extensions"
      val build_dir = tmp_dir + Path.basic(source_name)
      val build_script = "./configure " + build_options + " && make && make install"
      Isabelle_System.bash(build_script,
        cwd = build_dir.file,
        progress_stdout = progress.echo_if(verbose, _),
        progress_stderr = progress.echo_if(verbose, _)).check


      /* install */

      Isabelle_System.copy_file(build_dir + Path.explode("LICENSE"), component_dir)


      /* install packages */
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
    var requirements_file = Path.explode("$AFP_BASE/admin/sitegen-req.txt")
    var mirror = default_mirror
    var verbose = false

    val getopts = Getopts("""
Usage: isabelle afp_build_python [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -R FILE      requirements file (default "$AFP_BASE/admin/sitegen-req.txt")
    -U URL       download URL
                 (default """" + default_mirror + """")
    -v           verbose

  Build python component with virtual environment.
""",
      "D:" -> (arg => target_dir = Path.explode(arg)),
      "R:" -> (arg => requirements_file = Path.explode(arg)),
      "U:" -> (arg => mirror = arg),
      "v" -> (_ => verbose = true))

    getopts(args)

    val progress = new Console_Progress()

    build_python(requirements_file, progress, mirror, target_dir, verbose)
  })
}