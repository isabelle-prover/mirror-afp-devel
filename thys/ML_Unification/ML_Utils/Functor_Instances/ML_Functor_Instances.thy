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
    structure FIA : FUNCTOR_INSTANCE_ARGS
    val n : int
  end) =
  struct
    fun get_n () = (Pretty.writeln (Pretty.block
        [Pretty.str "retrieving n from ", Pretty.str A.FIA.full_name]);
      A.n)
  end

  \<comment>\<open>create an instance (structure) called \<open>Test_Functor_Instance\<close>\<close>
  @{functor_instance struct_name = Test_Functor_Instance
    and functor_name = My_Functor
    and id = \<open>"test"\<close>
    and more_args = \<open>val n = 42\<close>}

  val _ = Test_Functor_Instance.get_n ()
\<close>

end
