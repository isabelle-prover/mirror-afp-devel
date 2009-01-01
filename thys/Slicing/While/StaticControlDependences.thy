header {* \isaheader{Interpretations of the various static control dependences} *}

theory StaticControlDependences imports AdditionalLemmas 
  "../Basic/StandardControlDependence"
  "../Basic/WeakControlDependence"
begin

interpretation WStandardControlDependence:
  StandardControlDependencePDG "sourcenode" "targetnode" "kind" "valid_edge prog"
                    "Entry" "Exit" "Defs prog" "Uses prog" "id"
proof
  fix n assume "CFG.valid_node sourcenode targetnode (valid_edge prog) n"
  hence "valid_node prog n" by(simp add:valid_node_def While_CFG.valid_node_def)
  thus "\<exists>as. prog \<turnstile> (_Entry_) -as\<rightarrow>* n" by(rule valid_node_Entry_path)
next
  fix n assume "CFG.valid_node sourcenode targetnode (valid_edge prog) n"
  hence "valid_node prog n" by(simp add:valid_node_def While_CFG.valid_node_def)
  thus "\<exists>as. prog \<turnstile> n -as\<rightarrow>* (_Exit_)" by(rule valid_node_Exit_path)
qed

interpretation WWeakControlDependence:
  WeakControlDependencePDG "sourcenode" "targetnode" "kind" "valid_edge prog"
                    "Entry" "Exit" "Defs prog" "Uses prog" "id"
proof
  fix n assume "CFG.valid_node sourcenode targetnode (valid_edge prog) n"
  hence "valid_node prog n" by(simp add:valid_node_def While_CFG.valid_node_def)
  show "finite {n'. \<exists>a'. valid_edge prog a' \<and> sourcenode a' = n \<and>
                         targetnode a' = n'}"
    by(rule finite_successors)
qed

end