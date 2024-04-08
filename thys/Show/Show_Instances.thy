(*  Title:       Show
    Author:      Christian Sternagel <c.sternagel@gmail.com>
    Author:      René Thiemann <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel <c.sternagel@gmail.com>
    Maintainer:  René Thiemann <rene.thiemann@uibk.ac.at>
*)

section \<open>Instances of the Show Class for Standard Types\<close>

theory Show_Instances
  imports
    Show
    HOL.Rat
begin

definition showsp_unit :: "unit showsp"
  where
    "showsp_unit p x = shows_string ''()''"

lemma show_law_unit [show_law_intros]:
  "show_law showsp_unit x"
  by (rule show_lawI) (simp add: showsp_unit_def show_law_simps)

abbreviation showsp_char :: "char showsp"
  where
    "showsp_char \<equiv> shows_prec"

lemma show_law_char [show_law_intros]:
  "show_law showsp_char x"
  by (rule show_lawI) (simp add: show_law_simps)

primrec showsp_bool :: "bool showsp"
  where
    "showsp_bool p True = shows_string ''True''" |
    "showsp_bool p False = shows_string ''False''"

lemma show_law_bool [show_law_intros]:
  "show_law showsp_bool x"
  by (rule show_lawI, cases x) (simp_all add: show_law_simps)

primrec pshowsp_prod :: "(shows \<times> shows) showsp"
  where
    "pshowsp_prod p (x, y) = shows_string ''('' o x o shows_string '', '' o y o shows_string '')''"

(*NOTE: in order to be compatible with automatically generated show funtions,
show-arguments of "map"-functions need to get precedence 1 (which may lead to
redundant parentheses in the output, but seems unavoidable in the current setup,
i.e., pshowsp via primrec followed by defining showsp via pshowsp composed with map).*)
definition showsp_prod :: "'a showsp \<Rightarrow> 'b showsp \<Rightarrow> ('a \<times> 'b) showsp"
  where
    [code del]: "showsp_prod s1 s2 p = pshowsp_prod p o map_prod (s1 1) (s2 1)"

lemma showsp_prod_simps [simp, code]:
  "showsp_prod s1 s2 p (x, y) =
    shows_string ''('' o s1 1 x o shows_string '', '' o s2 1 y o shows_string '')''"
  by (simp add: showsp_prod_def)

lemma show_law_prod [show_law_intros]:
  "(\<And>x. x \<in> Basic_BNFs.fsts y \<Longrightarrow> show_law s1 x) \<Longrightarrow>
   (\<And>x. x \<in> Basic_BNFs.snds y \<Longrightarrow> show_law s2 x) \<Longrightarrow>
    show_law (showsp_prod s1 s2) y"
proof (induct y)
  case (Pair x y)
  note * = Pair [unfolded prod_set_simps]
  show ?case
    by (rule show_lawI)
      (auto simp del: o_apply intro!: o_append intro: show_lawD * simp: show_law_simps)
qed

fun string_of_digit :: "nat \<Rightarrow> string"
  where
    "string_of_digit n =
    (if n = 0 then ''0''
    else if n = 1 then ''1''
    else if n = 2 then ''2''
    else if n = 3 then ''3''
    else if n = 4 then ''4''
    else if n = 5 then ''5''
    else if n = 6 then ''6''
    else if n = 7 then ''7''
    else if n = 8 then ''8''
    else ''9'')"

fun showsp_nat :: "nat showsp"
  where
    "showsp_nat p n =
    (if n < 10 then shows_string (string_of_digit n)
    else showsp_nat p (n div 10) o shows_string (string_of_digit (n mod 10)))"
declare showsp_nat.simps [simp del]

lemma show_law_nat [show_law_intros]:
  "show_law showsp_nat n"
  by (rule show_lawI, induct n rule: nat_less_induct) (simp add: show_law_simps showsp_nat.simps)

lemma showsp_nat_append [show_law_simps]:
  "showsp_nat p n (x @ y) = showsp_nat p n x @ y"
  by (intro show_lawD show_law_intros)

definition showsp_int :: "int showsp"
  where
    "showsp_int p i =
    (if i < 0 then shows_string ''-'' o showsp_nat p (nat (- i)) else showsp_nat p (nat i))"

lemma show_law_int [show_law_intros]:
  "show_law showsp_int i"
  by (rule show_lawI, cases "i < 0") (simp_all add: showsp_int_def show_law_simps)

lemma showsp_int_append [show_law_simps]:
  "showsp_int p i (x @ y) = showsp_int p i x @ y"
  by (intro show_lawD show_law_intros)

definition showsp_rat :: "rat showsp"
  where
    "showsp_rat p x =
    (case quotient_of x of (d, n) \<Rightarrow>
      if n = 1 then showsp_int p d else showsp_int p d o shows_string ''/'' o showsp_int p n)"

lemma show_law_rat [show_law_intros]:
  "show_law showsp_rat r"
  by (rule show_lawI, cases "quotient_of r") (simp add: showsp_rat_def show_law_simps)

lemma showsp_rat_append [show_law_simps]:
  "showsp_rat p r (x @ y) = showsp_rat p r x @ y"
  by (intro show_lawD show_law_intros)

text \<open>
  Automatic show functions are not used for @{type unit}, @{type prod}, and numbers:
  for @{type unit} and @{type prod}, we do not want to display @{term "''Unity''"} and
  @{term "''Pair''"}; for @{type nat}, we do not want to display
  @{term "''Suc (Suc (... (Suc 0) ...))''"}; and neither @{type int}
  nor @{type rat} are datatypes.
\<close>

local_setup \<open>
  Show_Generator.register_foreign_partial_and_full_showsp @{type_name prod} 0
       @{term "pshowsp_prod"}
       @{term "showsp_prod"} (SOME @{thm showsp_prod_def})
       @{term "map_prod"} (SOME @{thm prod.map_comp}) [true, true]
       @{thm show_law_prod}
  #> Show_Generator.register_foreign_showsp @{typ unit} @{term "showsp_unit"} @{thm show_law_unit}
  #> Show_Generator.register_foreign_showsp @{typ bool} @{term "showsp_bool"} @{thm show_law_bool}
  #> Show_Generator.register_foreign_showsp @{typ char} @{term "showsp_char"} @{thm show_law_char}
  #> Show_Generator.register_foreign_showsp @{typ nat} @{term "showsp_nat"} @{thm show_law_nat}
  #> Show_Generator.register_foreign_showsp @{typ int} @{term "showsp_int"} @{thm show_law_int}
  #> Show_Generator.register_foreign_showsp @{typ rat} @{term "showsp_rat"} @{thm show_law_rat}
\<close>

derive "show" option sum prod unit bool nat int rat

export_code
  "shows_prec :: 'a::show option showsp"
  "shows_prec :: ('a::show, 'b::show) sum showsp"
  "shows_prec :: ('a::show \<times> 'b::show) showsp"
  "shows_prec :: unit showsp"
  "shows_prec :: char showsp"
  "shows_prec :: bool showsp"
  "shows_prec :: nat showsp"
  "shows_prec :: int showsp"
  "shows_prec :: rat showsp"
  checking

text \<open>In the sequel we prove injectivity of @{term "show :: nat \<Rightarrow> string"}.\<close>

lemma string_of_digit_inj:
  assumes "x < y \<and> y < 10"
  shows "string_of_digit x \<noteq> string_of_digit y"
  using assms
  apply (cases "y=1", simp)
  apply (cases "y=2", simp)
  apply (cases "y=3", simp)
  apply (cases "y=4", simp)
  apply (cases "y=5", simp)
  apply (cases "y=6", simp)
  apply (cases "y=7", simp)
  apply (cases "y=8", simp)
  apply (cases "y=9", simp)
  by arith


lemma string_of_digit_inj_2:
  assumes "x < 10"
  shows "length (string_of_digit x) = 1"
  using assms
  apply (cases "x=0", simp)
  apply (cases "x=1", simp)
  apply (cases "x=2", simp)
  apply (cases "x=3", simp)
  apply (cases "x=4", simp)
  apply (cases "x=5", simp)
  apply (cases "x=6", simp)
  apply (cases "x=7", simp)
  apply (cases "x=8", simp)
  apply (cases "x=9", simp)
  by arith

declare string_of_digit.simps[simp del]

lemma string_of_digit_inj_1:
  assumes "x < 10" and "y < 10" and "x \<noteq> y"
  shows "string_of_digit x \<noteq> string_of_digit y"
proof
  assume ass: "string_of_digit x = string_of_digit y"
  with assms have  "\<exists> xx yy :: nat. xx < 10 \<and> yy < 10 \<and> xx < yy \<and> string_of_digit xx = string_of_digit yy" 
  proof (cases "x < y", blast)
    case False
    with \<open>x \<noteq> y\<close> have "y < x" by arith
    with assms ass have "y < 10 \<and> x < 10 \<and> y < x \<and> string_of_digit y = string_of_digit x" by auto
    then show ?thesis by blast
  qed
  from this obtain xx yy :: nat where cond: "xx < 10 \<and> yy < 10 \<and> xx < yy \<and> string_of_digit xx = string_of_digit yy" by blast
  then show False using string_of_digit_inj by auto
qed

lemma shows_prec_nat_simp1:
  fixes n::nat assumes "\<not> n < 10" shows "shows_prec d n xs = ((shows_prec d (n div 10) \<circ> shows_string (string_of_digit (n mod 10)))) xs"
  using showsp_nat.simps[of d n]
  unfolding if_not_P[OF assms] shows_string_def o_def
  unfolding shows_prec_nat_def by simp

lemma show_nat_simp1: "\<not> (n::nat) < 10 \<Longrightarrow> show n = show (n div 10) @ string_of_digit (n mod 10)"
  using shows_prec_nat_simp1[of n "0::nat" "[]"] unfolding shows_string_def o_def
  unfolding shows_prec_append[symmetric] by simp

lemma show_nat_len_1: fixes x :: nat 
  shows "length (show x) > 0"
proof (cases "x < 10")
  assume ass: "\<not> x < 10"
  then have "show x = show (x div 10) @ string_of_digit (x mod 10)" by (rule show_nat_simp1)
  then have "length (show x) = length (show (x div 10)) + length (string_of_digit (x mod 10))"
    unfolding length_append[symmetric] by simp
  with ass show ?thesis by (simp add: string_of_digit_inj_2)
next
  assume "x < 10" then show ?thesis
    unfolding shows_prec_nat_def
    unfolding showsp_nat.simps[of 0 x]
    unfolding shows_string_def by (simp add: string_of_digit_inj_2)
qed

lemma shows_prec_nat_simp2:
  fixes n::nat assumes "n < 10" shows "shows_prec d n xs = string_of_digit n @ xs"
  using showsp_nat.simps[of d n]
  unfolding shows_prec_nat_def if_P[OF assms] shows_string_def by simp

lemma show_nat_simp2:
  fixes n::nat assumes "n < 10" shows "show n = string_of_digit n"
  using shows_prec_nat_simp2[OF assms, of "0::nat" "[]"] by simp

lemma show_nat_len_2:
  fixes x :: nat 
  assumes one: "length (show x) = 1" 
  shows "x < 10"
proof (rule ccontr)
  assume ass: "\<not> x < 10"
  then have "show x = show (x div 10) @ string_of_digit (x mod 10)" by (rule show_nat_simp1)
  then have "length (show x) = length (show (x div 10)) + length (string_of_digit (x mod 10))"
    unfolding length_append[symmetric] by simp
  with one have "length (show (x div 10)) = 0" by (simp add: string_of_digit_inj_2)
  with show_nat_len_1 show False by best
qed

lemma show_nat_len_3:
  fixes x :: nat 
  assumes one: "length (show x) > 1"
  shows "\<not> x < 10"
proof 
  assume ass: "x < 10"
  then have "show x = string_of_digit x" by (rule show_nat_simp2)
  with string_of_digit_inj_2 ass have "length (show x) = 1" by simp
  with one show False by arith
qed

lemma inj_show_nat: "inj (show::nat \<Rightarrow> string)"
  unfolding inj_on_def
proof (clarify)
  fix x y :: nat assume "show x = show y"
  then obtain n where "length (show x) = n \<and> show x = show y" by blast
  then show "x = y" 
  proof (induct n arbitrary: x y)
    case 0
    fix x y :: nat
    assume ass: "length (show x) = 0 \<and> show x = show y"
    then show ?case using show_nat_len_1 by best
  next
    case (Suc n)
    then have eq: "show x = show y" by blast
    from Suc have len: "length (show x) = Suc n" by blast
    show ?case
    proof (cases n)
      case 0
      with Suc have one: "length(show x) = 1 \<and> length (show y) = 1" by (auto)
      with show_nat_len_2 have ten: "x < 10 \<and> y < 10" by simp
      show ?thesis 
      proof (cases "x = y", simp)
        case False
        with ten string_of_digit_inj_1 have "string_of_digit x \<noteq> string_of_digit y" by auto
        with ten eq show ?thesis using show_nat_simp2[of x] show_nat_simp2[of y] by simp
      qed
    next
      case (Suc m)
      with len eq have "length (show x) = Suc (Suc m) \<and> length (show y) = Suc (Suc m)" by auto
      then have "length (show x) > 1 \<and> length (show y) > 1" by simp
      then have large: "\<not> x < 10 \<and> \<not> y < 10" using show_nat_len_3 by simp
      let ?e = "\<lambda>x::nat. show (x div 10) @ string_of_digit (x mod 10)"
      from large have id: "show x = ?e x \<and> show y = ?e y"
        using show_nat_simp1[of x] show_nat_simp1[of y] by auto
      from string_of_digit_inj_2 have one: "length (string_of_digit(x mod 10)) = 1
        \<and> length(string_of_digit(y mod 10)) = 1" by auto
      from one have "\<exists>xx. string_of_digit(x mod 10) = [xx]"
        by (cases "string_of_digit (x mod 10)",simp,cases "tl (string_of_digit (x mod 10))",simp,simp)
      from this obtain xx where xx: "string_of_digit(x mod 10) = [xx]" ..
      from one have "\<exists>xx. string_of_digit(y mod 10) = [xx]"
        by (cases "string_of_digit (y mod 10)",simp,cases "tl (string_of_digit (y mod 10))",simp,simp)
      from this obtain yy where yy: "string_of_digit(y mod 10) = [yy]" ..
      from id have "length (show x) = length (show (x div 10)) + length (string_of_digit (x mod 10))" unfolding length_append[symmetric] by simp
      with one len have shorter: "length (show (x div 10)) = n" by simp
      from eq id xx yy
      have "(show (x div 10) @ [xx]) = (show (y div 10) @ [yy])" by simp
      then have "(show (x div 10) = show(y div 10)) \<and> xx = yy" by clarify
      then have nearly: "show (x div 10) = show (y div 10)
        \<and> string_of_digit(x mod 10) = string_of_digit(y mod 10)" using xx yy by simp
      with shorter and
        \<open>length (show (x div 10)) = n \<and> show (x div 10) = show (y div 10) \<Longrightarrow> x div 10 = y div 10\<close>
      have div: "x div 10 = y div 10" by blast
      from nearly string_of_digit_inj_1 have mod:  "x mod 10 = y mod 10"
        by (cases "x mod 10 = y mod 10", simp, simp)
      have "x = 10 * (x div 10) + (x mod 10)" by auto
      also have "\<dots> = 10 * (y div 10) + (y mod 10)" using div mod by auto
      also have "\<dots> = y" by auto
      finally show ?thesis .
    qed
  qed
qed

end

