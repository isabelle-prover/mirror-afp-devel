/* Author: Fabian Huch

Miscellaneous AFP system operations.
*/
package afp


import isabelle.*


object AFP_System {
  def hg_id: String =
    if (Mercurial.Hg_Sync.ok(AFP.BASE)) File.read(AFP.BASE + Mercurial.Hg_Sync.PATH_ID)
    else AFP.self_repository().id()
}