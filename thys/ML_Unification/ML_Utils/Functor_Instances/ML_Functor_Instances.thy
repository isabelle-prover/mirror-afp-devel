\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>ML Functor Instances\<close>
theory ML_Functor_Instances
  imports
    ML_Parsing_Utils
begin

paragraph \<open>Summary\<close>
text \<open>Utilities for ML functors that create context data.\<close>

ML_file\<open>functor_instance.ML\<close>
ML_file\<open>functor_instance_antiquot.ML\<close>

paragraph \<open>Example\<close>

ML_command\<open>
  \<comment>\<open>some arbitrary functor\<close>
  functor My_Functor(A : sig
    structure FI : FUNCTOR_INSTANCE_BASE
    val n : int
  end) =
  struct
    fun get_n () = (Pretty.writeln (Pretty.block [
        Pretty.str "retrieving n from ", Binding.pretty A.FI.binding,
        Pretty.str " with id ", Pretty.str (quote A.FI.id)
      ]);
      A.n)
  end

  \<comment>\<open>create an instance (structure) called \<open>Test_Functor_Instance\<close>\<close>
structure A =
struct
\<^functor_instance>\<open>struct_name: Test
  functor_name: My_Functor
  path: \<open>"A"\<close>
  id: \<open>"test"\<close>
  more_args: \<open>val n = 42\<close>\<close>
end
  val _ = A.Test.get_n ()
\<close>

end
