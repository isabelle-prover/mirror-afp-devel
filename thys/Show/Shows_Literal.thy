(*  Title:       Shows_Literal
    Author:      René Thiemann <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann <rene.thiemann@uibk.ac.at>
*)

section \<open>Show Based on String Literals\<close>

theory Shows_Literal
  imports
    Main
    Show_Instances
begin

text \<open>In this theory we provide an alternative to the @{class show}-class, where
  @{typ String.literal} instead of @{typ string} is used, with the aim that target-language
  readable strings are used in generated code. In particular when writing Isabelle functions that
  produce strings such as @{term "STR ''this is info for the user: ...''"}, 
  this class might be useful.

  To keep it simple, in contrast to @{class show}, here we do not enforce the show law.\<close>


type_synonym showsl = "String.literal \<Rightarrow> String.literal" 

definition showsl_of_shows :: "shows \<Rightarrow> showsl" where
  "showsl_of_shows shws s = String.implode (shws []) + s" 

definition showsl_lit :: "String.literal \<Rightarrow> showsl" where
  "showsl_lit = (+)" 

definition "showsl_paren s = showsl_lit (STR ''('') o s o showsl_lit (STR '')'')"

fun showsl_sep :: "('a \<Rightarrow> showsl) \<Rightarrow> showsl \<Rightarrow> 'a list \<Rightarrow> showsl"
where
  "showsl_sep s sep [] = showsl_lit (STR '''')" |
  "showsl_sep s sep [x] = s x" |
  "showsl_sep s sep (x#xs) = s x o sep o showsl_sep s sep xs"

definition
  showsl_list_gen :: "('a \<Rightarrow> showsl) \<Rightarrow> String.literal \<Rightarrow> String.literal 
    \<Rightarrow> String.literal \<Rightarrow> String.literal \<Rightarrow> 'a list \<Rightarrow> showsl"
where
  "showsl_list_gen showslx e l s r xs =
    (if xs = [] then showsl_lit e
    else showsl_lit l o showsl_sep showslx (showsl_lit s) xs o showsl_lit r)"

definition default_showsl_list :: "('a \<Rightarrow> showsl) \<Rightarrow> 'a list \<Rightarrow> showsl" where
  "default_showsl_list sl = showsl_list_gen sl (STR ''[]'') (STR ''['') (STR '', '') (STR '']'')" 

definition [code_unfold]: "char_zero = (48 :: integer)" 

lemma char_zero: "char_zero = integer_of_char (CHR ''0'')" by code_simp
 
fun lit_of_digit :: "nat \<Rightarrow> String.literal" where
  "lit_of_digit n = 
    String.implode [char_of_integer (char_zero + integer_of_nat n)]"

class showl =
  fixes showsl :: "'a \<Rightarrow> showsl" 
  and showsl_list :: "'a list \<Rightarrow> showsl"  

definition "showsl_lines desc_empty = showsl_list_gen showsl desc_empty (STR '''') (STR ''\<newline>'') (STR '''')"

abbreviation showl where "showl x \<equiv> showsl x (STR '''')"

instantiation char :: showl
begin
definition "showsl_char c = showsl_lit (String.implode [c])" \<comment> \<open>Shouldn't there be a faster conversion than via strings?\<close>
definition "showsl_list_char cs s = showsl_lit (String.implode cs) s"
instance ..
end

instantiation String.literal :: showl
begin
definition "showsl (s :: String.literal) = showsl_lit s" 
definition "showsl_list (xs :: String.literal list) = default_showsl_list showsl xs" 
instance ..
end

instantiation bool :: showl
begin
definition "showsl (b :: bool) = showsl_lit (if b then STR ''True'' else STR ''False'')" 
definition "showsl_list (xs :: bool list) = default_showsl_list showsl xs" 
instance ..
end

instantiation nat :: showl
begin
fun showsl_nat :: "nat \<Rightarrow> showsl" where
  "showsl_nat n =
    (if n < 10 then showsl_lit (lit_of_digit n)
    else showsl_nat (n div 10) o showsl_lit (lit_of_digit (n mod 10)))"
definition "showsl_list (xs :: nat list) = default_showsl_list showsl xs"
instance ..
end

instantiation int :: showl
begin
definition "showsl_int i =
    (if i < 0 then showsl_lit (STR ''-'') o showsl (nat (- i)) else showsl (nat i))" 
definition "showsl_list (xs :: int list) = default_showsl_list showsl xs"
instance ..
end

instantiation integer :: showl
begin
definition showsl_integer :: "integer \<Rightarrow> showsl" where "showsl_integer i = showsl (int_of_integer i)" 
definition showsl_list_integer :: "integer list \<Rightarrow> showsl" where "showsl_list_integer xs = default_showsl_list showsl xs" 
instance ..
end


instantiation rat :: showl
begin
definition "showsl_rat x =
    (case quotient_of x of (d, n) \<Rightarrow>
      if n = 1 then showsl d else showsl d o showsl_lit (STR ''/'') o showsl n)"
definition "showsl_list (xs :: rat list) = default_showsl_list showsl xs"
instance ..
end

instantiation unit :: showl
begin
definition "showsl (x :: unit) = showsl_lit (STR ''()'')" 
definition "showsl_list (xs :: unit list) = default_showsl_list showsl xs"
instance ..
end

instantiation option :: (showl) showl
begin
fun showsl_option where
  "showsl_option None = showsl_lit (STR ''None'')" 
| "showsl_option (Some x) = showsl_lit (STR ''Some ('') o showsl x o showsl_lit (STR '')'')" 
definition "showsl_list (xs :: 'a option list) = default_showsl_list showsl xs"
instance ..
end

instantiation sum :: (showl,showl) showl
begin
fun showsl_sum where
  "showsl_sum (Inl x) = showsl_lit (STR ''Inl ('') o showsl x o showsl_lit (STR '')'')" 
| "showsl_sum (Inr x) = showsl_lit (STR ''Inr ('') o showsl x o showsl_lit (STR '')'')" 
definition "showsl_list (xs :: ('a + 'b) list) = default_showsl_list showsl xs"
instance ..
end

instantiation prod :: (showl,showl) showl
begin
fun showsl_prod where
  "showsl_prod (Pair x y) = showsl_lit (STR ''('') o showsl x 
        o showsl_lit (STR '', '') o showsl y o showsl_lit (STR '')'')"  
definition "showsl_list (xs :: ('a * 'b) list) = default_showsl_list showsl xs"
instance ..
end

definition [code_unfold]: "showsl_nl = showsl (STR ''\<newline>'')" 

definition add_index :: "showsl \<Rightarrow> nat \<Rightarrow> showsl" where
  "add_index s i = s o showsl_lit (STR ''.'') o showsl i"


instantiation list :: (showl) showl
begin
definition showsl_list :: "'a list \<Rightarrow> showsl" where 
  "showsl_list (xs :: 'a list) = showl_class.showsl_list xs"  
definition "showsl_list_list (xs :: 'a list list) = default_showsl_list showsl xs"
instance ..
end

end
