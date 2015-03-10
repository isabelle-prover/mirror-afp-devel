theory Compare_Instances
imports
  Compare_Generator
begin

section \<open>Defining comparators for standard types\<close>

text \<open>For all of the following types, we define comparators and register them in the class 
  @{class compare}:
  @{type int}, @{type nat}, @{type bool}, @{type unit}, @{type sum}, @{type option}, @{type list},
  and @{type prod}. For all but @{type prod}, we also register in class @{class compare_order}.\<close>

text \<open>For @{type int} and @{type nat} we just use their linear orders as comparators.\<close>
derive (linorder) compare_order int nat

text \<open>For @{type sum}, @{type list}, and @{type option} we generate comparators which are then
  utilized to define linear orders on these types.\<close>
derive compare_order sum list option

text \<open>For @{type prod} we just generate a comparator, but do not define the linear order,
  in order to not raise any conflicts with the class-instantiations for @{type prod} that
  are provided in the Isabelle distribution.\<close>
derive compare prod

text \<open>We do not use the linear order to define the comparator for @{typ bool} and @{typ unit}, 
  but implement more efficient ones.\<close>

fun comparator_unit :: "unit comparator" where
  "comparator_unit x y = Eq"

fun comparator_bool :: "bool comparator" where
  "comparator_bool False False = Eq"
| "comparator_bool False True = Lt"
| "comparator_bool True True = Eq"
| "comparator_bool True False = Gt"

lemma comparator_unit: "comparator comparator_unit"
  by (unfold_locales, auto)

lemma comparator_bool: "comparator comparator_bool"
proof
  fix x y z :: bool
  show "sym_order (comparator_bool x y) = comparator_bool y x" by (cases x, (cases y, auto)+)
  show "comparator_bool x y = Eq \<Longrightarrow> x = y" by (cases x, (cases y, auto)+)
  show "comparator_bool x y = Lt \<Longrightarrow> comparator_bool y z = Lt \<Longrightarrow> comparator_bool x z = Lt"
    by (cases x, (cases y, auto), cases y, (cases z, auto)+)
qed


local_setup {*
  Comparator_Generator.register_foreign_comparator @{typ unit}
    @{term comparator_unit}
    @{thm comparator_unit}
*}

local_setup {*
  Comparator_Generator.register_foreign_comparator @{typ bool}
    @{term comparator_bool}
    @{thm comparator_bool}
*}

derive compare bool unit

text \<open>It is not directly possible to "derive (linorder) bool/unit", since 
  @{term "compare :: bool comparator"}
  was not defined as @{term "comparator_of :: bool comparator"}, but as
  @{const comparator_bool}.
  However, we can manually prove this equivalence
  and then use this knowledge to prove the instance of @{class compare_order}.\<close>

lemma comparator_bool_comparator_of [compare_simps]:
  "comparator_bool = comparator_of"
proof (intro ext)
  fix a b 
  show "comparator_bool a b = comparator_of a b"
    unfolding comparator_of_def
    by (cases a, (cases b, auto))
qed

lemma comparator_unit_comparator_of [compare_simps]:
  "comparator_unit = comparator_of"
proof (intro ext)
  fix a b 
  show "comparator_unit a b = comparator_of a b"
    unfolding comparator_of_def by auto
qed

derive (linorder) compare_order bool unit
end