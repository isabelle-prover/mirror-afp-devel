(*  Title:       Derive_Manager
    Author:      René Thiemann <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

section \<open>Derive manager\<close>

theory Derive_Manager
imports Main
keywords "print_derives" :: diag and "derive" :: thy_decl
begin

ML_file "derive_aux.ML" 
ML_file "derive_manager.ML"

text \<open>
The derive manager allows to install various deriving-commands, e.g., to derive 
orders, pretty-printer, hash-functions, \ldots. -functions. All of the registered commands
are then accessible via the \texttt{derive}-command, e.g., \texttt{derive hashable list}
would automatically derive a hash-function for the datatype \texttt{list}.

There is also the diagnostic command \texttt{print-derives} which shows a list of options
what can currently be derived.
\<close>

end
