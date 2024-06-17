(*  Title:       RTSCat_Interp
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2024
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Top-Level Interpretation"

theory RTSCat_Interp
imports RTSCatx RTSCat
begin

  text\<open>
    The purpose of this section is simply to demonstrate the possibility of making
    top-level interpretations of locales @{locale rtscatx} and @{locale rtscat}.
    It is important to do this because some kinds of clashes that occur when the same names
    are used in multiple sublocales only cause a problem when an attempt is made to instantiate
    the locale in the top-level name space.
  \<close>

  interpretation RTSx: rtscatx \<open>TYPE(V)\<close>
  proof -
    interpret V: universe \<open>TYPE(V)\<close>
      using V_is_universe by auto
    show "rtscatx (TYPE(V))" ..
  qed

  interpretation RTS: rtscat \<open>TYPE(V)\<close>
  proof -
    interpret V: universe \<open>TYPE(V)\<close>
      using V_is_universe by auto
    show "rtscat (TYPE(V))" ..
  qed

end
