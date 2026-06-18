/* Author: Fabian Huch

Miscellaneous AFP system operations.
*/
package afp


import isabelle.*


object AFP_System {
  def repository(): Mercurial.Repository = Mercurial.repository(AFP.BASE)

  def hg_id(): String =
    if (Mercurial.Hg_Sync.ok(AFP.BASE)) File.read(AFP.BASE + Mercurial.Hg_Sync.PATH_ID)
    else repository().id()

  def afp_version: String = Isabelle_System.getenv_strict("AFP_VERSION")
  def afp_name: String = "afp-" + afp_version

  def AFP_BUILD_OPTIONS: List[Options.Spec] =
    Word.explode(Isabelle_System.getenv("AFP_BUILD_OPTIONS")).map(Options.Spec.make)
}