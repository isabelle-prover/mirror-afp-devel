package afp


import isabelle._


object AFP_Dependencies
{
  def as_json(entry: String, distrib_deps: List[String], afp_deps: List[String]): String =
    s"""
      {"$entry":
        {"distrib_deps": [${commas_quote(distrib_deps)}],
         "afp_deps": [${commas_quote(afp_deps)}]
        }
      }"""

  def afp_dependencies(afp_dir: Path): String =
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

    val result = selected.groupBy(get_entry).collect {
      case (Some(e), sessions) =>
        val dependencies = sessions.flatMap(tree.imports_graph.imm_preds)
          .map(d => (d, get_entry(d)))
        val distrib_deps = dependencies.collect { case (d, None) => d }.distinct
        val afp_deps = dependencies.collect { case (_, Some(d)) if d != e => d }.distinct
        as_json(e, distrib_deps, afp_deps)
    }

    "[" + commas(result) + "]"
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

        val res = afp_dependencies(afp_dir)
        output_file match {
          case Some(file) => File.write(file, res)
          case None => progress.echo(res)
        }
      }
    )
}
