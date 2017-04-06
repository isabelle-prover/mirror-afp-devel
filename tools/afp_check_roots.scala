// DESCRIPTION: check ROOT files of AFP sessions

object AFP_Check_Roots extends isabelle.Isabelle_Tool.Body {

  import isabelle._

  val afp_dir = Path.explode("$AFP")

  def print_good(string: String): Unit =
    println(Console.BOLD + Console.GREEN + string + Console.RESET)

  def print_bad(string: String): Unit =
    println(Console.BOLD + Console.RED + string + Console.RESET)

  def check_timeout(tree: Sessions.T, selected: List[String]): Boolean =
    selected.flatMap { name =>
      val info = tree(name)
      val entry = info.dir.base.implode
      if (info.options.real("timeout") == 0)
        Some((entry, name))
      else
        None
    } match {
      case Nil =>
        print_good("All sessions specify a timeout.")
        true
      case offenders =>
        print_bad("The following entries contain sessions without timeouts:")
        offenders.groupBy(_._1).mapValues(_.map(_._2)).foreach { case (entry, sessions) =>
          println(s"""  $entry ${sessions.mkString("(", ", ", ")")}""")
        }
        false
    }

  def check_paths(tree: Sessions.T, selected: List[String]): Boolean =
    selected.flatMap { name =>
      val info = tree(name)
      val dir = info.dir
      if (dir.dir.implode != afp_dir.implode)
        Some((name, dir))
      else
        None
    } match {
      case Nil =>
        print_good("All sessions are in the correct directory.")
        true
      case offenders =>
        print_bad("The following sessions are in the wrong directory:")
        offenders.foreach { case (session, dir) =>
          println(s"  $session ($dir)")
        }
        false
    }

  def check_chapter(tree: Sessions.T, selected: List[String]): Boolean =
    selected.flatMap { name =>
      val info = tree(name)
      val entry = info.dir.base.implode
      if (info.chapter != "AFP")
        Some(entry)
      else
        None
    }.distinct match {
      case Nil =>
        print_good("All entries are in the 'AFP' chapter.")
        true
      case offenders =>
        print_bad("The following entries are not in the AFP chapter:")
        offenders.foreach { entry => println(s"""  $entry""") }
        false
    }

  def check_groups(tree: Sessions.T, selected: List[String]): Boolean =
    selected.flatMap { name =>
      val info = tree(name)
      if (!info.groups.toSet.subsetOf(Set("AFP", "slow", "very_slow")) ||
          !info.groups.contains("AFP"))
        Some((name, info.groups))
      else
        None
    } match {
      case Nil =>
        print_good("All sessions have correct groups.")
        true
      case offenders =>
        print_bad("The following sessions have wrong groups:")
        offenders.foreach { case (session, groups) =>
          println(s"""  $session ${groups.mkString("{", ", ", "}")}""")
        }
        false
    }


  def apply(args: List[String]): Unit =
  {
    val full_tree = Sessions.load(Options.init(), Nil, List(afp_dir))
    val (selected, _) = full_tree.selection(false, false, Nil, Nil, Nil, Nil)

    val checks = List(
      check_timeout(full_tree, selected),
      check_paths(full_tree, selected),
      check_chapter(full_tree, selected),
      check_groups(full_tree, selected))

    if (checks.exists(!_))
    {
      print_bad("Errors found.")
      System.exit(1)
    }
  }

}
