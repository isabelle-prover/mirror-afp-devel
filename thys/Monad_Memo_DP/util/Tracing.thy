theory Tracing
  imports
    "../heap_monad/Heap_Main"
    "HOL-Library.Code_Target_Numeral"
begin

text \<open>NB:
  There is also the more complete entry \<^url>\<open>https://www.isa-afp.org/entries/Show.html\<close>,
  but we avoid the dependency of the AFP here.
\<close>

definition writeln :: "String.literal \<Rightarrow> unit" where
  "writeln = (\<lambda> s. ())"

code_printing
  constant writeln \<rightharpoonup> (SML) "writeln _"

definition trace where
  "trace s x = (let a = writeln s in x)"

lemma trace_alt_def[simp]:
  "trace s x = (\<lambda> _. x) (writeln s)"
  unfolding trace_def by simp

definition (in heap_mem_defs) checkmem_trace ::
  "('k \<Rightarrow> String.literal) \<Rightarrow> 'k \<Rightarrow> (unit \<Rightarrow> 'v Heap) \<Rightarrow> 'v Heap"
  where
  "checkmem_trace trace_key param calc \<equiv>
    Heap_Monad.bind (lookup param) (\<lambda> x.
    case x of
      Some x \<Rightarrow> trace (STR ''Hit '' + trace_key param) (return x)
    | None \<Rightarrow> trace (STR ''Miss ''  + trace_key param)
       Heap_Monad.bind (calc ()) (\<lambda> x.
        Heap_Monad.bind (update param x) (\<lambda> _.
        return x
      )
    )
  )
  "

lemma (in heap_mem_defs) checkmem_checkmem_trace:
  "checkmem param calc = checkmem_trace trace_key param (\<lambda>_. calc)"
  unfolding checkmem_trace_def checkmem_def trace_alt_def ..

fun nat_to_string :: "nat \<Rightarrow> String.literal" where
  "nat_to_string 0 = STR ''''" |
  "nat_to_string (Suc i) = STR ''I'' + nat_to_string i"

definition nat_pair_to_string :: "nat \<times> nat \<Rightarrow> String.literal" where
  "nat_pair_to_string = (\<lambda> (m, n).
    STR ''('' + nat_to_string m + STR '', '' + nat_to_string n + STR '')'')"

code_printing
  constant nat_to_string \<rightharpoonup> (SML) "Int.toString (case _ of Nat x => x)"

paragraph \<open>Code Setup\<close>

lemmas [code] =
  heap_mem_defs.checkmem_trace_def

lemmas [code_unfold] =
  heap_mem_defs.checkmem_checkmem_trace[where trace_key = nat_to_string]
  heap_mem_defs.checkmem_checkmem_trace[where trace_key = nat_pair_to_string]

end
