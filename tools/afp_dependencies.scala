package afp


import Metadata.Entry


import isabelle._


object AFP_Dependencies
{
  case class Dependency(entry: Entry.Name,  distrib_deps: List[Entry.Name], afp_deps: List[Entry.Name])

  object JSON
  {
    private def from_dep(dependency: Dependency): (String, isabelle.JSON.T) =
      dependency.entry ->
        isabelle.JSON.Object(
          "distrib_deps" -> dependency.distrib_deps,
          "afp_deps" -> dependency.afp_deps
        )

    def from_dependency(dep: Dependency): isabelle.JSON.T =
      isabelle.JSON.Object(from_dep(dep))

    def from_dependencies(deps: List[Dependency]): isabelle.JSON.T =
      deps.map(from_dep).toMap
  }

  def afp_dependencies(afp_dir: Path): List[Dependency] =
  {
    val tree = Sessions.load_structure(Options.init(), Nil, List(afp_dir))
    val selected = tree.selection(Sessions.Selection(false, false, Nil, Nil, Nil, Nil))
      .build_graph.keys

    def get_entry(name: String): Option[String] =
    {
      val info = tree(name)
      val dir = info.dir

      if (selected.contains(dir.dir.expand))
        None
      else
        Some(dir.base.implode)
    }

    selected.groupBy(get_entry).toList.map {
      case (Some(e), sessions) =>
        val dependencies = sessions.flatMap(tree.imports_graph.imm_preds)
          .map(d => (d, get_entry(d)))
        val distrib_deps = dependencies.collect { case (d, None) => d }.distinct
        val afp_deps = dependencies.collect { case (_, Some(d)) if d != e => d }.distinct
        Dependency(e, distrib_deps, afp_deps)
    }
  }

  val isabelle_tool =
    Isabelle_Tool(
      "afp_dependencies",
      "extract dependencies between AFP entries",
      Scala_Project.here,
      args => {
        var output_file: Option[Path] = None

        val getopts = Getopts(
          """
Usage: isabelle afp_dependencies [OPTIONS]

  Options are:
    -o FILE      output file name

  Extract dependencies between AFP entries.
""",
          "o:" -> (arg => output_file = Some(Path.explode(arg)))
        )

        getopts(args)
        val afp_dir = Path.explode("$AFP").expand

        val progress = new Console_Progress()

        val res = afp_dependencies(afp_dir).map(JSON.from_dependency)
        val json = isabelle.JSON.Format(res)

        output_file match {
          case Some(file) => File.write(file, json)
          case None => progress.echo(json)
        }
      }
    )
}
