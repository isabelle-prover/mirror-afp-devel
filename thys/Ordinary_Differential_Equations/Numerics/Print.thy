section {* Target Language debug messages *}
theory Print
imports
  "../../Affine_Arithmetic/Executable_Euclidean_Space"
begin

text {* very ad-hoc... *}

subsection {* Printing *}

text {* Just for debugging purposes *}

definition print::"String.literal \<Rightarrow> unit" where "print x = ()"

definition int_to_string::"int \<Rightarrow> String.literal"
  where "int_to_string x = STR ''''"

context includes integer.lifting begin

lift_definition integer_to_string::"integer \<Rightarrow> String.literal"
  is int_to_string .

end

lemma [code]: "integer_to_string x = STR ''''"
  by (simp add: integer_to_string_def int_to_string_def)

lemma [code]: "int_to_string x = integer_to_string (integer_of_int x)"
  by (simp add: integer_to_string_def)

definition "println x = (let _ = print x in print (STR ''\<newline>''))"

code_printing
  constant print \<rightharpoonup> (SML) "TextIO.print"
| constant "integer_to_string :: integer \<Rightarrow> String.literal" \<rightharpoonup> (SML) "Int.toString"

consts float2_float10::"int \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> int \<Rightarrow> (int * int)"

context includes integer.lifting begin

lift_definition float2_float10_integer::"integer \<Rightarrow> bool \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> (integer * integer)"
  is float2_float10 .

lemma float2_float10_code[code]: "float2_float10 x b m e =
  (case float2_float10_integer (integer_of_int x) b (integer_of_int m) (integer_of_int e) of (a, b) \<Rightarrow>
  (int_of_integer a, int_of_integer b))"
  by transfer simp

end

code_printing
  code_module "Float2_Float10" \<rightharpoonup> (SML)
  --"this is taken from Approximation.thy" --"TODO: implement in Isabelle/HOL?"
{*
fun float2float10integer prec round_down m e = (
  let
    val (m, e) = (if e < 0 then (m,e) else (m * IntInf.pow (2, e), 0))

    fun frac c p 0 digits cnt = (digits, cnt, 0)
      | frac c 0 r digits cnt = (digits, cnt, r)
      | frac c p r digits cnt = (let
        val (d, r) = IntInf.divMod (r * 10, IntInf.pow (2, ~e))
      in frac (c orelse d <> 0) (if d <> 0 orelse c then p - 1 else p) r
              (digits * 10 + d) (cnt + 1)
      end)

    val sgn = Int.sign m
    val m = abs m

    val round_down = (sgn = 1 andalso round_down) orelse
                     (sgn = ~1 andalso not round_down)

    val (x, r) = IntInf.divMod (m, (IntInf.pow (2, ~e)))

    val p = ((if x = 0 then prec else prec - (IntInf.log2 x + 1)) * 3) div 10 + 1

    val (digits, e10, r) = if p > 0 then frac (x <> 0) p r 0 0 else (0,0,0)

    val digits = if round_down orelse r = 0 then digits else digits + 1

  in (sgn * (digits + x * (IntInf.pow (10, e10))), ~e10)
  end)
*}
| constant float2_float10_integer \<rightharpoonup> (SML) "float2float10integer"
code_reserved SML float2_float10_integer

definition print_real::"real \<Rightarrow> unit" where "print_real x = ()"

lemma print_Floatreal[code]:
  "print_real (FloatR a b) =
    (let
      (m, e) = float2_float10 25 True a b;
      _ = print (int_to_string m);
      _ = print (STR ''e'');
      _ = print (int_to_string e)
     in
       ())"
  by simp_all

definition print_eucl::"'a::executable_euclidean_space \<Rightarrow> unit"
  where "print_eucl x =
    (let
      _ = print (STR ''('');
      _ = map (\<lambda>i. let _ = print_real (x \<bullet> i); _ = print (STR '', '') in ()) (Basis_list::'a list);
      _ = print (STR '')'')
    in ())"

definition bind_err:: "String.literal \<Rightarrow> 'c option \<Rightarrow> ('c \<Rightarrow> 'd option) \<Rightarrow> 'd option"
  where [simp]: "bind_err err = Option.bind"

lemma [code]:
  "bind_err err None f = (let _ = println err in None)"
  "bind_err err (Some x) f = f x"
  by auto

end
