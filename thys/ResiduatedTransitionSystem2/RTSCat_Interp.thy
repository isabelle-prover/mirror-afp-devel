(*  Title:       RTSCat_Interp
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2024
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Top-Level Interpretation"

theory RTSCat_Interp
imports RTSCat_trn RTSCat_sim
begin

  text\<open>
    The purpose of this section is simply to demonstrate the possibility of making
    top-level interpretations of locales @{locale rtscat_trn} and @{locale rtscat_sim}.
    It is important to do this because some kinds of clashes that occur when the same names
    are used in multiple sublocales only cause a problem when an attempt is made to instantiate
    the locale in the top-level name space.
  \<close>

  interpretation RTS\<^sub>t\<^sub>r\<^sub>n: rtscat_trn \<open>TYPE(V)\<close>
  proof -
    interpret V: universe \<open>TYPE(V)\<close>
      using V_is_universe by auto
    show "rtscat_trn (TYPE(V))" ..
  qed

  interpretation RT\<^sub>s\<^sub>i\<^sub>m: rtscat_sim \<open>TYPE(V)\<close>
  proof -
    interpret V: universe \<open>TYPE(V)\<close>
      using V_is_universe by auto
    show "rtscat_sim (TYPE(V))" ..
  qed

end
