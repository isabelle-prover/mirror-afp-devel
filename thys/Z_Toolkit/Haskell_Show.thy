section \<open> Show class for code generation \<close>

theory Haskell_Show
  imports "HOL-Library.Code_Target_Int" "HOL-Library.Code_Target_Nat"
begin

text \<open> The aim of this theory is support code generation of serialisers for datatypes using the
  Haskell show class. We take inspiration from \<^url>\<open>https://www.isa-afp.org/entries/Show.html\<close>, but
  we are more interested in code generation than being able to derive the show function for 
  any algebraic datatype. Sometimes we give actual instance that can reasoned about in Isabelle,
  but mostly opaque types and code printing to Haskell instance is sufficient. \<close>

subsection \<open> Show class \<close>

text \<open> The following class should correspond to the Haskell type class Show, but currently it
       has only part of the signature. \<close>

class "show" =
  fixes "show" :: "'a \<Rightarrow> String.literal" \<comment> \<open> We use @{typ String.literal} for code generation \<close>

text \<open> We set up code printing so that this class, and the constants therein, are mapped to the
  Haskell Show class. \<close>

code_printing
  type_class "show" \<rightharpoonup> (Haskell) "Prelude.Show"
| constant "show" \<rightharpoonup> (Haskell) "Prelude.show"

subsection \<open> Instances \<close>

text \<open> We create an instance for bool, that generates an Isabelle function. \<close>

instantiation bool :: "show"
begin

fun show_bool :: "bool \<Rightarrow> String.literal" where
"show_bool True = STR ''True''" |
"show_bool False = STR ''False''"

instance ..

end

text \<open> We map the instance for bool to the built-in Haskell show, and have the code generator
  use the built-in class instance. \<close>

code_printing
  constant "show_bool_inst.show_bool" \<rightharpoonup> (Haskell) "Prelude.show"
| class_instance "bool" :: "show" \<rightharpoonup> (Haskell) -

instantiation unit :: "show"
begin

fun show_unit :: "unit \<Rightarrow> String.literal" where
"show_unit () = STR ''()''"

instance ..

end

code_printing
  constant "show_unit_inst.show_unit" \<rightharpoonup> (Haskell) "Prelude.show"
| class_instance "unit" :: "show" \<rightharpoonup> (Haskell) -

text \<open> Actually, we don't really need to create the show function if all we're interested in is
  code generation. Here, for the @{typ integer} instance, we omit the definition. This is
  because @{typ integer} is set up to correspond to the built-in Haskell type Integer, which
  already has a Show instance. \<close>

instantiation integer :: "show"
begin

instance ..

end

text \<open> For the code generator, the crucial line follows. This maps the (unspecified) Isabelle show
  function to the Haskell show function, which is built-in. We also specify that no instance of
  Show should be generated for integer, as it exists already. \<close>

code_printing
  constant "show_integer_inst.show_integer" \<rightharpoonup> (Haskell) "Prelude.show"
| class_instance "integer" :: "show" \<rightharpoonup> (Haskell) -

text \<open> For @{typ int}, we are effectively dealing with a packaged version of @{typ integer} in
  the code generation set up. So, we simply define show in terms of the "underlying" integer
  using @{const integer_of_int}. \<close>

instantiation int :: "show"
begin

definition show_int :: "int \<Rightarrow> String.literal" where
"show_int x = show (integer_of_int x)"

instance ..

end

text \<open> As a result, we can prove a code equation that will mean that our show instance for @{typ int}
  simply calls the built-in show function for @{typ integer}. \<close>

lemma show_int_of_integer [code]: "show (int_of_integer x) = show x" 
  by (simp add: show_int_def)

instantiation nat :: "show"
begin

definition show_nat :: "nat \<Rightarrow> String.literal" where
"show_nat x = show (integer_of_nat x)"

instance ..

end

lemma show_Nat: "show (Nat x) = show (max 0 x)"
  using Code_Target_Nat.Nat_def integer_of_nat_eq_of_nat nat_of_integer_def of_nat_of_integer show_nat_def by presburger
  
instantiation String.literal :: "show"
begin

definition show_literal :: "String.literal \<Rightarrow> String.literal" where
"show_literal x = STR ''\"'' + x + STR ''\"''"

instance ..

end

code_printing
  constant "show_literal_inst.show_literal" \<rightharpoonup> (Haskell) "Prelude.show"
| class_instance "String.literal" :: "show" \<rightharpoonup> (Haskell) -


instantiation prod :: ("show", "show") "show"
begin

instance ..

end

code_printing
  constant "show_prod_inst.show_prod" \<rightharpoonup> (Haskell) "Prelude.show"
| class_instance "prod" :: "show" \<rightharpoonup> (Haskell) -

instantiation list :: ("show") "show"
begin

instance ..

end

code_printing
  constant "show_list_inst.show_list" \<rightharpoonup> (Haskell) "Prelude.show"
| class_instance "list" :: "show" \<rightharpoonup> (Haskell) -

end