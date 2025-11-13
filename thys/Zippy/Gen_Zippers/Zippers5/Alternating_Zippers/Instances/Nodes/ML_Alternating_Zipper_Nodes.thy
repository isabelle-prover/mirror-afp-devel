\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_Alternating_Zipper_Nodes
  imports
    ML_Alternating_Zippers
begin

ML_gen_file\<open>node.ML\<close>
ML_gen_file\<open>modify_node_content.ML\<close>
ML_gen_file\<open>modify_node_next.ML\<close>

setup\<open>fn theory =>
let val nzippers = ML_Gen.nzippers () + 1
in Context.theory_map (ML_Gen.setup_zipper_args' (NONE, NONE) (SOME nzippers, NONE)) theory end\<close>
text \<open>Note: we reload the ML file @{file node.ML}, just with different parameters.\<close>
ML_gen_file\<open>node.ML\<close>
ML\<open>
  val succ_node_sig = sfx_T_nargs "NODE"
  val succ_node_functor = sfx_T_nargs "Node"
\<close>
setup\<open>fn theory =>
let val nzippers = ML_Gen.nzippers () - 1
in Context.theory_map (ML_Gen.setup_zipper_args' (NONE, NONE) (SOME nzippers, NONE)) theory end\<close>

context
  notes [[imap stop: \<open>ML_Gen.nzippers () + 1\<close>]]
begin
ML_gen_file\<open>instantiate_node_succ.ML\<close>
end

ML_gen_file\<open>alternating_zipper_nodes.ML\<close>
ML_gen_file\<open>alternating_zipper_nodes_zippers.ML\<close>
ML_gen_file\<open>alternating_zipper_nodes_simple_zippers.ML\<close>

end
