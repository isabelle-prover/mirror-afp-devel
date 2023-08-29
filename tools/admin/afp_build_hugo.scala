package afp


import isabelle._


object AFP_Build_Hugo {
  val default_mirror = "https://github.com/gohugoio/hugo/releases/download/v0.88.1"

  def make_component_name(version: String): String = "hugo-" + version

  def make_archive_name(release: String, platform: Platform.Family): String = {
    val arch = platform match {
      case isabelle.Platform.Family.linux => "Linux-64bit"
      case isabelle.Platform.Family.macos => "macOS-64bit"
      case _ => error("Unsupported platform: " + platform)
    }
    "hugo_extended_" + release + "_" + arch + ".tar.gz"
  }

  def build_hugo(
    progress: Progress = new Progress,
    mirror: String = default_mirror,
    target_dir: Path = Path.current
  ): Unit = {
    Isabelle_System.with_tmp_dir("hugo") { tmp_dir =>
      /* component */

      val Version = """^.*?v([^/]+)$""".r
      val version =
        mirror match {
          case Version(version) => version
          case _ => error("Failed to determine component version from " + quote(mirror))
        }

      val component = make_component_name(version)
      val component_dir = Isabelle_System.new_directory(target_dir.absolute + Path.basic(component))
      progress.echo("Component " + component_dir)


      /* platform */

      val platform_name =
        proper_string(Isabelle_System.getenv("ISABELLE_PLATFORM64")) getOrElse
          error("No 64bit platform")

      val platform_dir = Isabelle_System.make_directory(component_dir + Path.basic(platform_name))


      /* archive */

      val platform = Platform.Family.values.find(Platform.Family.standard(_) == platform_name).get

      val archive_name = make_archive_name(version, platform)


      /* download */

      val archive_path = tmp_dir + Path.basic(archive_name)
      val download_url = mirror + "/" + archive_name
      Isabelle_System.download_file(download_url, archive_path, progress = progress)

      Isabelle_System.bash("tar xzf " + File.bash_path(archive_path), cwd = tmp_dir.file).check


      /* install */

      Isabelle_System.copy_file(tmp_dir + Path.explode("hugo"), platform_dir)
      Isabelle_System.copy_file(tmp_dir + Path.explode("LICENSE"), component_dir)


      /* settings */

      val etc_dir = Isabelle_System.make_directory(component_dir + Path.basic("etc"))
      File.write(etc_dir + Path.basic("settings"),
        """# -*- shell-script -*- :mode=shellscript:

ISABELLE_HUGO="$COMPONENT/$ISABELLE_PLATFORM64"
""")


      /* README */

      File.write(component_dir + Path.basic("README"),
        "This Isabelle components provides a hugo extended " + version +
          """ component from """ + mirror + """

        Fabian
        """ + Date.Format.date(Date.now()) + "\n")
    }
  }

  val isabelle_tool = Isabelle_Tool("afp_build_hugo", "build afp hugo component",
    Scala_Project.here,
  { args =>
    var target_dir = Path.current
    var mirror = default_mirror

    val getopts = Getopts("""
Usage: isabelle afp_build_hugo [OPTIONS]

  Options are:
    -D DIR       target directory (default ".")
    -U URL       release mirror
                 (default """ + mirror + """)

  Build extended hugo component.
""",
      "D:" -> (arg => target_dir = Path.explode(arg)),
      "U:" -> (arg => mirror = arg))

    getopts(args)

    val progress = new Console_Progress()

    build_hugo(progress = progress, mirror = mirror, target_dir = target_dir)
  })
}