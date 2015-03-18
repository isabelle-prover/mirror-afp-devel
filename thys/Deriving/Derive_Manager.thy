(*  Title:       Deriving class instances for datatypes
    Author:      Christian Sternagel and René Thiemann  <christian.sternagel|rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann 
    License:     LGPL
*)
section \<open>Derive Manager\<close>

theory Derive_Manager
imports Main
keywords "print_derives" :: diag and "derive" :: thy_decl
begin

text \<open>
  The derive manager allows the user to register various derive-hooks, e.g., for orders,
  pretty-printers, hash-functions, etc. All registered hooks are accessible via the derive command.

  @{rail \<open>
    @'derive' ('(' param ')')? sort (datatype+)
  \<close>}

  \begin{description}
  \item @{text "\<^bold>d\<^bold>e\<^bold>r\<^bold>i\<^bold>v\<^bold>e (param) sort datatype"} calls the hook for deriving @{text sort} (that
  may depend on the optional @{text param}) on @{text datatype} (if such a hook is registered).

  E.g., @{text "\<^bold>d\<^bold>e\<^bold>r\<^bold>i\<^bold>v\<^bold>e compare_order list"} will derive a comparator for datatype @{type list}
  which is also used to define a linear order on @{type list}s.
  \end{description}

  There is also the diagnostic command @{text "\<^bold>p\<^bold>r\<^bold>i\<^bold>n\<^bold>t\<^bold>_\<^bold>d\<^bold>e\<^bold>r\<^bold>i\<^bold>v\<^bold>e\<^bold>s"} that shows the list of currently
  registered hooks.
\<close>

ML_file "derive_manager.ML"

end
