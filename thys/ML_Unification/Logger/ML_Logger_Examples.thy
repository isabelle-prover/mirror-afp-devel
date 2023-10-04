\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Examples\<close>
theory ML_Logger_Examples
  imports
    ML_Logger
    Setup_Result_Commands
begin

text \<open>First some simple, barebone logging: print some information.\<close>
ML_command\<open>
  \<comment> \<open>the following two are equivalent\<close>
  val _ = Logger.log Logger.root_logger Logger.INFO @{context} (K "hello root logger")
  val _ = @{log Logger.INFO Logger.root_logger} @{context} (K "hello root logger")
\<close>

ML_command\<open>
  val logger = Logger.root_logger
  val _ = @{log} @{context} (K "hello root logger")
  \<comment> \<open>\<open>@{log}\<close> is equivalent to \<open>Logger.log logger Logger.INFO\<close>\<close>
\<close>

text \<open>To guarantee the existence of a "logger" in an ML structure, one should use the
\<open>HAS_LOGGER\<close> signature.\<close>
ML\<open>
  structure My_Struct : sig
    include HAS_LOGGER
    val get_n :  Proof.context -> int
  end = struct
    val logger = Logger.setup_new_logger Logger.root_logger "My_Struct"
    fun get_n ctxt = (@{log} ctxt (K "retrieving n..."); 42)
  end
\<close>

ML_command\<open>val n = My_Struct.get_n @{context}\<close>

text\<open>We can set up a hierarchy of loggers\<close>
ML\<open>
  val logger = Logger.root_logger
  val parent1 = Logger.setup_new_logger Logger.root_logger "Parent1"
  val child1 = Logger.setup_new_logger parent1 "Child1"
  val child2 = Logger.setup_new_logger parent1 "Child2"

  val parent2 = Logger.setup_new_logger Logger.root_logger "Parent2"
\<close>

ML_command\<open>
  (@{log Logger.INFO Logger.root_logger} @{context} (K "Hello root logger");
  @{log Logger.INFO parent1} @{context} (K "Hello parent1");
  @{log Logger.INFO child1} @{context} (K "Hello child1");
  @{log Logger.INFO child2} @{context} (K "Hello child2");
  @{log Logger.INFO parent2} @{context} (K "Hello parent2"))
\<close>

text \<open>We can use different log levels to show/surpress messages. The log levels are based on
Apache's Log4J 2 \<^url>\<open>https://logging.apache.org/log4j/2.x/manual/customloglevels.html\<close>.\<close>
ML_command\<open>@{log Logger.DEBUG parent1} @{context} (K "Hello parent1")\<close> \<comment>\<open>prints nothings\<close>
declare [[ML_map_context \<open>Logger.set_log_level parent1 Logger.DEBUG\<close>]]
ML_command\<open>@{log Logger.DEBUG parent1} @{context} (K "Hello parent1")\<close> \<comment>\<open>prints message\<close>
ML_command\<open>Logger.ALL\<close> \<comment>\<open>ctrl+click on the value to see all log levels\<close>

text \<open>We can set options for all loggers below a given logger. Below, we set the log level for all
loggers below (and including) \<^ML>\<open>parent1\<close> to error, thus disabling warning messages.\<close>
ML_command\<open>
  (@{log Logger.WARN parent1} @{context} (K "Warning from parent1");
  @{log Logger.WARN child1} @{context} (K "Warning from child1"))
\<close>
declare [[ML_map_context \<open>Logger.set_log_levels parent1 Logger.ERR\<close>]]
ML_command\<open>
  (@{log Logger.WARN parent1} @{context} (K "Warning from parent1");
  @{log Logger.WARN child1} @{context} (K "Warning from child1"))
\<close>
declare [[ML_map_context \<open>Logger.set_log_levels parent1 Logger.INFO\<close>]]

text \<open>We can set message filters.\<close>

declare [[ML_map_context \<open>Logger.set_msg_filters Logger.root_logger (match_string "Third")\<close>]]
ML_command\<open>
  (@{log Logger.INFO parent1} @{context} (K "First message");
  @{log Logger.INFO child1} @{context} (K "Second message");
  @{log Logger.INFO child2} @{context} (K "Third message");
  @{log Logger.INFO parent2} @{context} (K "Fourth message"))
\<close>
declare [[ML_map_context \<open>Logger.set_msg_filters Logger.root_logger (K true)\<close>]]

text \<open>One can also use different output channels (e.g. files) and hide/show some additional
logging information. Ctrl+click on below values and explore.\<close>
ML_command\<open>Logger.set_output; Logger.set_show_logger; Logging_Antiquotation.show_log_pos\<close>

text \<open>To set up (local) loggers outside ML environments,
@{theory ML_Unification.Setup_Result_Commands} contains two commands,
@{command setup_result} and @{command local_setup_result}.\<close>
experiment
begin
local_setup_result local_logger = \<open>Logger.new_logger Logger.root_logger "Local"\<close>

ML_command\<open>@{log Logger.INFO local_logger} @{context} (K "Hello local world")\<close>
end

text \<open>\<open>local_logger\<close> is no longer available. The follow thus does not work:\<close>
\<comment> \<open>ML_command\<open>@{log Logger.INFO local_logger} @{context} (K "Hello local world")\<close>\<close>

text \<open>Let us create another logger in the global context.\<close>
setup_result some_logger = \<open>Logger.new_logger Logger.root_logger "Some_Logger"\<close>
ML_command\<open>@{log Logger.INFO some_logger} @{context} (K "Hello world")\<close>

text \<open>Let us delete it again.\<close>
declare [[ML_map_context \<open>Logger.delete_logger some_logger\<close>]]
text \<open>The logger can no longer be found in the logger hierarchy\<close>
ML_command\<open>@{log Logger.INFO some_logger} @{context} (K "Hello world")\<close>

end
