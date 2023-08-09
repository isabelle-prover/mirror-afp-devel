(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
License: LGPL
*)
subsection \<open>Make lists instances of the infinite-class.\<close>

theory Lists_are_Infinite
  imports Fresh_Identifiers.Fresh
begin

instance list :: (type) infinite
  by (intro_classes, rule infinite_UNIV_listI)

end