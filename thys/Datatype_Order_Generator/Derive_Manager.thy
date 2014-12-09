(*  Title:       Derive_Manager
    Author:      René Thiemann <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

section \<open>Derive Manager\<close>

theory Derive_Manager
imports Main
keywords "print_derives" :: diag and "derive" :: thy_decl
begin

ML_file "derive_aux.ML" 
ML_file "derive_manager.ML"

text \<open>
  The derive manager allows the user to register various derive-hooks, e.g., for orders,
  pretty-printers, hash-functions, etc. All registered hooks are accessible via the
  \texttt{derive}-command, e.g., @{text "derive hashable list"} automatically derives a
  hash-function for datatype @{type list}.

  There is also the diagnostic command \texttt{print\_derives} that shows the list of currently
  registered hooks.
\<close>

end
