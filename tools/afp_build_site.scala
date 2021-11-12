package afp


import isabelle._


object AFP_Build_Site
{
  def afp_build_site(
    out_dir: Path, layout: Hugo.Layout,
    do_watch: Boolean = false,
    progress: Progress = new Progress()): Unit =
  {
    if (do_watch) {
      Hugo.watch(layout, out_dir, progress).check
    } else {
      progress.echo("Building site...")

      Hugo.build(layout, out_dir).check

      progress.echo("Build in " + (out_dir + Path.basic("index.html")).absolute.implode)
    }
  }

  val isabelle_tool = Isabelle_Tool("afp_build_site", "build generated afp website source", Scala_Project.here, args =>
  {
    var hugo_dir = Path.explode("$AFP_BASE") + Path.make(List("web", "hugo"))
    var out_dir = Path.explode("$AFP_BASE") + Path.basic("web")
    var do_watch = false

    val getopts = Getopts("""
Usage: isabelle afp_build_site [OPTIONS]

  Options are:
    -H DIR       generated sources dir (default "$AFP_BASE/web/hugo")
    -O DIR       output dir (default "$AFP_BASE/web")
    -w           watch sources and serve result

  Build the AFP website from generated sources.
""",
      "H:" -> (arg => hugo_dir = Path.explode(arg)),
      "O:" -> (arg => out_dir = Path.explode(arg)),
      "w"  -> (_ => do_watch = true))

    getopts(args)

    val layout = Hugo.Layout(hugo_dir)
    val progress = new Console_Progress()

    afp_build_site(out_dir = out_dir, layout = layout, progress = progress, do_watch = do_watch)
  })
}