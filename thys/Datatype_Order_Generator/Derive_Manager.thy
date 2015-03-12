section \<open>Derive Manager\<close>

theory Derive_Manager
imports Main
keywords "print_derives" :: diag and "derive" :: thy_decl
begin

ML_file "derive_manager.ML"

text \<open>
  The derive manager allows the user to register various derive-hooks, e.g., for orders,
  pretty-printers, hash-functions, etc. All registered hooks are accessible via the derive command.

  @{rail \<open>
    @'derive' ('(' param ')')? sort (datatype+)
  \<close>}

  \begin{description}
  \item @{text "\<^bold>d\<^bold>e\<^bold>r\<^bold>i\<^bold>v\<^bold>e (param) sort datatype"} calls the hook for deriving @{text sort} (that
  may depend on the optional @{text param}) on @{text datatype} (if such a hook is registered).

  E.g., @{text "\<^bold>d\<^bold>e\<^bold>r\<^bold>i\<^bold>v\<^bold>e hashable list"} will derive a hash-function for datatype @{type list}.
  \end{description}

  There is also the diagnostic command @{text "\<^bold>p\<^bold>r\<^bold>i\<^bold>n\<^bold>t\<^bold>_\<^bold>d\<^bold>e\<^bold>r\<^bold>i\<^bold>v\<^bold>e\<^bold>s"} that shows the list of currently
  registered hooks.
\<close>

end
