/* Author: Fabian Huch

Miscellaneous AFP system operations.
*/
package afp


import isabelle.*


object AFP_System {
  def hg_id: String =
    if (Mercurial.Hg_Sync.ok(AFP.BASE)) File.read(AFP.BASE + Mercurial.Hg_Sync.PATH_ID)
    else Mercurial.repository(AFP.BASE).id()

  def afp_version: String = Isabelle_System.getenv_strict("AFP_VERSION")
  def afp_name: String = "afp-" + afp_version
}