section \<open>Target Language debug messages\<close>
theory Print
imports
  "~~/src/HOL/Decision_Procs/Approximation"
  "../../Affine_Arithmetic/Affine_Arithmetic"
  "../../Show/Show_Instances"
  "~~/src/HOL/Library/Monad_Syntax"
  "Optimize_Integer"
  "~~/src/HOL/Library/Code_Char"
begin

subsection \<open>Printing\<close>

text \<open>Just for debugging purposes\<close>

definition print::"String.literal \<Rightarrow> unit" where "print x = ()"

context includes integer.lifting begin

end

code_printing constant print \<rightharpoonup> (SML) "TextIO.print"


subsection \<open>Write to File\<close>

definition file_append::"String.literal \<Rightarrow> String.literal \<Rightarrow> unit" where "file_append x y = ()"
code_printing constant file_append \<rightharpoonup> (SML) "(File.append o Path.explode)"

definition file_write::"String.literal \<Rightarrow> String.literal \<Rightarrow> unit" where "file_write x y = ()"
code_printing constant file_write \<rightharpoonup> (SML) "(File.write o Path.explode)"

  
subsection \<open>Show for Floats\<close>

definition showsp_float :: "float showsp"
where
  "showsp_float p x = (
    let m = mantissa x; e = exponent x in
      if e = 0 then showsp_int p m else showsp_int p m o shows_string ''*2^'' o showsp_int p e)"

lemma show_law_float [show_law_intros]:
  "show_law showsp_float r"
  by (auto simp: showsp_float_def Let_def show_law_simps intro!: show_lawI)

lemma showsp_float_append [show_law_simps]:
  "showsp_float p r (x @ y) = showsp_float p r x @ y"
  by (intro show_lawD show_law_intros)

local_setup \<open>Show_Generator.register_foreign_showsp @{typ float} @{term "showsp_float"} @{thm show_law_float}\<close>

derive "show" float


subsection \<open>Convert Float to Decimal number\<close>

text \<open>type for decimal floating point numbers
  (currently just for printing, TODO? generalize theory Float for arbitrary base)\<close>

datatype float10 = Float10 (mantissa10: int) (exponent10: int)
notation Float10 (infix "\<e>" 999)

partial_function (tailrec) normalize_float10
  where [code]: "normalize_float10 f =
    (if mantissa10 f mod 10 \<noteq> 0 \<or> mantissa10 f = 0 then f
    else normalize_float10 (Float10 (mantissa10 f div 20) (exponent10 f + 1)))"

subsubsection \<open>Version that should be easy to prove correct, but slow!\<close>

definition "float_to_float10_approximation f = the
  (do {
    let (x, y) = (mantissa f * 1024, exponent f - 10);
    let p = nat (bitlen (abs x) + bitlen (abs y) + 80);(* FIXME: are there guarantees? *)
    y_log \<leftarrow> approx p (Approximation.Mult (Approximation.Num (of_int y))
      ((Approximation.Mult (Approximation.Ln (Approximation.Num 2))
        (Approximation.Inverse (Approximation.Ln (Approximation.Num 10)))))) [];
    let e_fl = floor_fl (fst y_log);
    let e = int_floor_fl e_fl;
    (ml, mu) \<leftarrow> approx p (Approximation.Mult (Approximation.Num (of_int x)) (Powr (Approximation.Num 10) (Approximation.Add(Approximation.Var 0) (Approximation.Minus (Approximation.Num e_fl))))) [Some y_log];
    Some (normalize_float10 (Float10 (int_floor_fl ml) e), normalize_float10 (Float10 (- int_floor_fl (- mu)) e))
  })"

lemma compute_float_of[code]: "float_of (real_of_float f) = f" by simp


subsection \<open>Trusted, but faster version\<close>

text \<open>TODO: this is the HOL version of the SML-code in Approximation.thy\<close>

lemma prod_case_call_mono[partial_function_mono]:
  "mono_tailrec (\<lambda>f. (let (d, e) = a in (\<lambda>y. f (c d e y))) b)"
  by (simp add: split_beta' call_mono)

definition divmod_int::"int \<Rightarrow> int \<Rightarrow> int * int"
where "divmod_int a b = (a div b, a mod b)"

partial_function (tailrec) f2f10_frac where
 "f2f10_frac c p r digits cnt e =
    (if r = 0 then (digits, cnt, 0)
    else if p = 0 then (digits, cnt, r)
    else (let
      (d, r) = divmod_int (r * 10) (power_int 2 (-e))
    in f2f10_frac (c \<or> d \<noteq> 0) (if d \<noteq> 0 \<or> c then p - 1 else p) r
      (digits * 10 + d) (cnt + 1)) e)"
declare f2f10_frac.simps[code]

definition float2_float10::"int \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> int \<Rightarrow> (int * int)" where
  "float2_float10 prec rd m e = (
  let
    (m, e) = (if e < 0 then (m,e) else (m * power_int 2 e, 0));
    sgn = sgn m;
    m = abs m;

    round_down = (sgn = 1 \<and> rd) \<or> (sgn = -1 \<and> \<not> rd);

    (x, r) = divmod_int m ((power_int 2 (-e)));

    p = ((if x = 0 then prec else prec - (log2 x + 1)) * 3) div 10 + 1;

    (digits, e10, r) = if p > 0 then f2f10_frac (x \<noteq> 0) p r 0 0 e else (0,0,0);

    digits = if round_down \<or> r = 0 then digits else digits + 1

  in (sgn * (digits + x * (power_int 10 e10)), -e10))"

definition "lfloat10 r = (let f = float_of r in case_prod Float10 (float2_float10 20 True (mantissa f) (exponent f)))"
definition "ufloat10 r = (let f = float_of r in case_prod Float10 (float2_float10 20 False (mantissa f) (exponent f)))"

partial_function (tailrec) digits
  where [code]: "digits m ds = (if m = 0 then ds else digits (m div 10) (m mod 10 # ds))"

primrec showsp_float10 :: "float10 showsp"
where
  "showsp_float10 p (Float10 m e) = (
    let
      ds = digits (nat (abs m)) [];
      d = int (length ds);
      e = e + d - 1;
      mp = take 1 ds;
      ms = drop 1 ds;
      ms = rev (dropWhile (op = 0) (rev ms));
      show_digits = shows_list_gen (showsp_nat p) ''0'' '''' '''' ''''
    in (if m < 0 then shows_string ''-'' else (\<lambda>x. x)) o
        show_digits mp o
        (if ms = [] then (\<lambda>x. x) else shows_string ''.'' o show_digits ms) o
        (if e = 0 then (\<lambda>x. x) else shows_string ''e'' o showsp_int p e))"

lemma show_law_float10_aux:
  fixes m e
  shows "show_law showsp_float10 (Float10 m e)"
  apply (rule show_lawI)
  unfolding showsp_float10.simps Let_def
  apply (simp add: show_law_simps )
  done

lemma show_law_float10 [show_law_intros]: "show_law showsp_float10 r"
  by (cases r) (auto simp: show_law_float10_aux)

lemma showsp_float10_append [show_law_simps]:
  "showsp_float10 p r (x @ y) = showsp_float10 p r x @ y"
  by (intro show_lawD show_law_intros)

local_setup \<open>Show_Generator.register_foreign_showsp @{typ float10} @{term "showsp_float10"} @{thm show_law_float10}\<close>

derive "show" float10


subsection \<open>gnuplot output\<close>

definition lshows_eucl::"'a::executable_euclidean_space \<Rightarrow> shows"
where "lshows_eucl x = shows_words (map (\<lambda>i. lfloat10 (x \<bullet> i)) (Basis_list::'a list))"
abbreviation "lshow_eucl x \<equiv> lshows_eucl x ''''"
definition ushows_eucl::"'a::executable_euclidean_space \<Rightarrow> shows"
where "ushows_eucl x = shows_words (map (\<lambda>i. ufloat10 (x \<bullet> i)) (Basis_list::'a list))"
abbreviation "ushow_eucl x \<equiv> ushows_eucl x ''''"


subsubsection \<open>vector output of 2D zonotope\<close>

definition shows_segments_of_aform
where "shows_segments_of_aform a b x =
  shows_list_gen id '''' '''' ''\<newline>'' ''\<newline>'' (map (\<lambda>((x0, y0), (x1, y1)). shows_words (map lfloat10 [x0, y0, x1 - x0, y1 - y0]))
    (segments_of_aform (inner2_aform x a b)))"
abbreviation "show_segments_of_aform a b x \<equiv> shows_segments_of_aform a b x ''''"

definition shows_box_of_aform\<comment>\<open>box and some further information\<close>
where "shows_box_of_aform X = (let
    R = Radius' 20 X;
    l = fst X - R;
    u = fst X + R
    in shows_list_gen id '''' '''' '' '' '''' (lshows_eucl l # map ushows_eucl [u, R, snd (max_pdev (snd X))]) o shows_space o
      shows (ufloat10 (infnorm R)) o shows_space o
      shows (length (list_of_pdevs (snd X))) o
      shows_nl
    )"
abbreviation "show_box_of_aform x \<equiv> shows_box_of_aform x ''''"

definition shows_box_of_aform_hr\<comment>\<open>human readable\<close>
where "shows_box_of_aform_hr X = (let
    R = Radius' 20 X;
    l = fst X - R;
    u = fst X + R
    in shows_paren (lshows_eucl l) o shows_string '' .. '' o shows_paren (ushows_eucl u) o
      shows_string ''; devs: '' o shows (length (list_of_pdevs (snd X))) o
      shows_string ''; width: '' o shows (ufloat10 (infnorm R)) o
      shows_string ''; tdev: '' o shows_paren (ushows_eucl R) o
      shows_string ''; maxdev: '' o shows_paren (lshows_eucl (snd (max_pdev (snd X)))) o
      shows_nl
    )"
abbreviation "show_box_of_aform_hr x \<equiv> shows_box_of_aform_hr x ''''"

definition shows_aform_hr\<comment>\<open>human readable\<close>
where "shows_aform_hr X =
    shows_paren (lshows_eucl (fst X)) o shows_string '' ++ '' o
    shows_list_gen id ''[]'' ''[('' ''), ('' '')]'' (map (lshows_eucl o snd) (list_of_pdevs (snd X))) o
    shows_nl"

abbreviation "show_aform_hr x \<equiv> shows_aform_hr x ''''"

subsection \<open>Tracing for ODE solver\<close>

definition "trace_verbose msg X =
  print (String.implode
    ((shows_string msg o shows_nl o
      (case X of Some X \<Rightarrow> shows_box_of_aform_hr X o shows_aform_hr X | None \<Rightarrow> id)) ''\<newline>''))"

end
