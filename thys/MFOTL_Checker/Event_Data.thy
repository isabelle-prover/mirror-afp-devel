(*<*)
theory Event_Data
  imports
    "HOL-Library.Char_ord"
begin
(*>*)

section \<open>Type of Events\<close>

subsection \<open>Code Adaptation for 8-bit strings\<close>

typedef string8 = "UNIV :: char list set" ..

setup_lifting type_definition_string8

lift_definition empty_string :: string8 is "[]" .
lift_definition string8_literal :: "String.literal \<Rightarrow> string8" is String.explode .
lift_definition literal_string8:: "string8 \<Rightarrow> String.literal" is String.Abs_literal .
declare [[coercion string8_literal]]

instantiation string8 :: "{equal, linorder}"
begin

lift_definition equal_string8 :: "string8 \<Rightarrow> string8 \<Rightarrow> bool" is HOL.equal .
lift_definition less_eq_string8 :: "string8 \<Rightarrow> string8 \<Rightarrow> bool" is ord_class.lexordp_eq .
lift_definition less_string8 :: "string8 \<Rightarrow> string8 \<Rightarrow> bool" is ord_class.lexordp .

instance by intro_classes
    (transfer; auto simp: equal_eq lexordp_conv_lexordp_eq lexordp_eq_linear
      intro: lexordp_eq_refl lexordp_eq_trans lexordp_eq_antisym)+

end

lifting_forget string8.lifting

declare [[code drop: literal_string8 string8_literal "HOL.equal :: string8 \<Rightarrow> _"
      "(\<le>) :: string8 \<Rightarrow> _" "(<) :: string8 \<Rightarrow> _"
      "Code_Evaluation.term_of :: string8 \<Rightarrow> _"]]

code_printing
  type_constructor string8 \<rightharpoonup> (OCaml) "string"
  | constant "HOL.equal :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (OCaml) "Stdlib.(=)"
  | constant "(\<le>) :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (OCaml) "Stdlib.(<=)"
  | constant "(<) :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (OCaml) "Stdlib.(<)"
  | constant "empty_string :: string8" \<rightharpoonup> (OCaml) "\"\""
  | constant "string8_literal :: String.literal \<Rightarrow> string8" \<rightharpoonup> (OCaml) "id"
  | constant "literal_string8 :: string8 \<Rightarrow> String.literal" \<rightharpoonup> (OCaml) "id"

ML \<open>structure String8 = struct fun to_term x = @{term Abs_string8} $ HOLogic.mk_string x; end;\<close>

code_printing
  type_constructor string8 \<rightharpoonup> (Eval) "string"
  | constant "string8_literal :: String.literal \<Rightarrow> string8" \<rightharpoonup> (Eval) "_"
  | constant "HOL.equal :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (Eval) infixl 6 "="
  | constant "(\<le>) :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (Eval) infixl 6 "<="
  | constant "(<) :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (Eval) infixl 6 "<"
  | constant "empty_string :: string8" \<rightharpoonup> (Eval) "\"\""
  | constant "Code_Evaluation.term_of :: string8 \<Rightarrow> term" \<rightharpoonup> (Eval) "String8.to'_term"

ML \<open>structure String8 =struct fun to_term x = @{term Abs_string8} $ HOLogic.mk_string x; end;\<close>

code_printing
  type_constructor string8 \<rightharpoonup> (Eval) "string"
  | constant "string8_literal :: String.literal \<Rightarrow> string8" \<rightharpoonup> (Eval) "_"
  | constant "HOL.equal :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (Eval) infixl 6 "="
  | constant "(\<le>) :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (Eval) infixl 6 "<="
  | constant "(<) :: string8 \<Rightarrow> string8 \<Rightarrow> bool" \<rightharpoonup> (Eval) infixl 6 "<"
  | constant "Code_Evaluation.term_of :: string8 \<Rightarrow> term" \<rightharpoonup> (Eval) "String8.to'_term"

subsection \<open>Event Parameters\<close>

definition div_to_zero :: "integer \<Rightarrow> integer \<Rightarrow> integer" where
  "div_to_zero x y = (let z = fst (Code_Numeral.divmod_abs x y) in
    if (x < 0) \<noteq> (y < 0) then - z else z)"

definition mod_to_zero :: "integer \<Rightarrow> integer \<Rightarrow> integer" where
  "mod_to_zero x y = (let z = snd (Code_Numeral.divmod_abs x y) in
    if x < 0 then - z else z)"

lemma "b \<noteq> 0 \<Longrightarrow> div_to_zero a b * b + mod_to_zero a b = a"
  unfolding div_to_zero_def mod_to_zero_def Let_def
  by (auto simp: minus_mod_eq_mult_div[symmetric] div_minus_right mod_minus_right ac_simps)

datatype event_data = EInt integer | EString string8

instantiation event_data :: "{ord, plus, minus, uminus, times, divide, modulo}"
begin

fun less_eq_event_data where
  "EInt x \<le> EInt y \<longleftrightarrow> x \<le> y"
| "EString x \<le> EString y \<longleftrightarrow> x \<le> y"
| "EInt _ \<le> EString _ \<longleftrightarrow> True"
| "(_ :: event_data) \<le> _ \<longleftrightarrow> False"

definition less_event_data :: "event_data \<Rightarrow> event_data \<Rightarrow> bool" where
  "less_event_data x y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

fun plus_event_data where
  "EInt x + EInt y = EInt (x + y)"
| "(_::event_data) + _ = undefined"

fun minus_event_data where
  "EInt x - EInt y = EInt (x - y)"
| "(_::event_data) - _ = undefined"

fun uminus_event_data where
  "- EInt x = EInt (- x)"
| "- (_::event_data) = undefined"

fun times_event_data where
  "EInt x * EInt y = EInt (x * y)"
| "(_::event_data) * _ = undefined"

fun divide_event_data where
  "EInt x div EInt y = EInt (div_to_zero x y)"
| "(_::event_data) div _ = undefined"

fun modulo_event_data where
  "EInt x mod EInt y = EInt (mod_to_zero x y)"
| "(_::event_data) mod _ = undefined"

instance ..

end

lemma infinite_UNIV_event_data:
  "\<not>finite (UNIV :: event_data set)"
proof -
  define f where "f = (\<lambda>k. EInt k)"
  have inj: "inj_on f (UNIV :: integer set)"
    unfolding f_def by (meson event_data.inject(1) injI)
  show ?thesis using finite_imageD[OF _ inj]
    by (meson infinite_UNIV_char_0 infinite_iff_countable_subset top_greatest)
qed

primrec integer_of_event_data :: "event_data \<Rightarrow> integer" where
  "integer_of_event_data (EInt _) = undefined"
| "integer_of_event_data (EString _) = undefined"

instantiation event_data :: default begin

definition default_event_data :: event_data where "default = EInt 0"

instance proof qed

end

instantiation event_data :: linorder begin
instance
proof (standard, unfold less_event_data_def, goal_cases less refl trans antisym total)
  case (refl x)
  then show ?case
    by (cases x) auto
next
  case (trans x y z)
  then show ?case
    by (cases x; cases y; cases z) auto
next
  case (antisym x y)
  then show ?case
    by (cases x; cases y) auto
next
  case (total x y)
  then show ?case
    by (cases x; cases y) auto
qed simp

end


(*<*)
end
(*>*)
