(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Unique Factorization Domain\<close>

text\<open>This theory provides a definition of a unique factorization domain (UFD)
  for type-based integral domains. It is built upon the existing 
  carrier-based definition of UFDs in HOL-algebra (factorial-monoid).\<close>

theory Unique_Factorization_Domain
imports
  "~~/src/HOL/Number_Theory/Primes"
  "../Jordan_Normal_Form/Missing_Fraction_Field"
  "../Polynomial_Interpolation/Ring_Hom_Poly"
  "~~/src/HOL/Algebra/Divisibility"
begin

lemma dvd_field: "((x :: 'a :: field) dvd y) = (x = 0 \<longrightarrow> y = 0)"
  unfolding dvd_def 
  by (auto, intro exI[of _ "inverse x * y"], auto)

class ufd = idom +
  assumes factorial: "factorial_monoid \<lparr> carrier = UNIV - {0}, mult = op *, one = 1 \<rparr>"

abbreviation "mk_monoid \<equiv> \<lparr>carrier = UNIV - {0}, mult = op *, one = 1\<rparr>"

lemma carrier_0[simp]: "x \<in> carrier mk_monoid = (x \<noteq> 0)" by auto

lemmas mk_monoid_simps = carrier_0 monoid.simps

abbreviation irreducible where "irreducible \<equiv> Divisibility.irreducible mk_monoid"
abbreviation factor where "factor \<equiv> Divisibility.factor mk_monoid"
abbreviation factors where "factors \<equiv> Divisibility.factors mk_monoid"
abbreviation properfactor where "properfactor \<equiv> Divisibility.properfactor mk_monoid"

lemma properfactor_nz: "(y :: 'a :: {one,mult_zero,Rings.dvd}) \<noteq> 0 \<Longrightarrow> properfactor x y = (x dvd y \<and> \<not> y dvd x)"
  unfolding properfactor_def factor_def dvd_def
  by auto

lemma factor_idom: "factor (x::'a::idom) y = (if y = 0 then x = 0 else (x dvd y))"
  unfolding factor_def dvd_def
  by (cases "y = 0", auto, intro exI[of _ 1], auto)

lemma factor_idom_nz: "(y::'a::idom) \<noteq> 0 \<Longrightarrow> factor x y = (x dvd y)" 
  unfolding factor_idom by auto

lemma units_idom_nz: "(y::'a::idom) \<noteq> 0 \<Longrightarrow> y \<in> Units mk_monoid = (y dvd 1)"
  unfolding dvd_def Units_def by (auto simp: ac_simps)

lemma irreducible_idom_nz: assumes y: "(y::'a::idom) \<noteq> 0"
  shows "irreducible y = (\<not> y dvd 1 \<and> (\<forall> b. b dvd y \<longrightarrow> \<not> y dvd b \<longrightarrow> b dvd 1))"
  unfolding irreducible_def units_idom_nz[OF y] properfactor_nz[OF y]
  by (auto simp: units_idom_nz)

lemma factors: 
  "factors fs y = (listprod fs = y \<and> Ball (set fs) irreducible)"
proof -
  have "listprod fs = foldr op * fs 1" by (induct fs, auto)
  thus ?thesis unfolding factors_def by auto
qed

lemmas idom_nz =
  factor_idom_nz
  units_idom_nz 
  properfactor_nz
  irreducible_idom_nz

lemma comm_monoid_cancel_idom: "comm_monoid_cancel (mk_monoid::'a::idom monoid)"
  by (unfold_locales, auto)

instantiation int :: ufd begin

lemma Units_int: "(x \<in> Units (mk_monoid::int monoid)) = (x \<noteq> 0 \<and> (x = 1 \<or> x = -1))"
  unfolding Units_def by (auto simp: zmult_eq_1_iff) 

lemma prime_int: "Divisibility.prime (mk_monoid::int monoid) (x :: int) = (x = 0 \<or> Primes.prime (nat (abs x)))" (is "?l = ?r")
proof (cases "x = 0 \<or> x = 1 \<or> x = -1")
  case True
  thus ?thesis unfolding Divisibility.prime_def factor_idom Units_int 
    by (cases "x = 0", auto)
next
  case False
  hence l: "?l = ((\<forall> a b. a \<noteq> 0 \<longrightarrow> b \<noteq> 0 \<longrightarrow> x dvd a * b \<longrightarrow> x dvd a \<or> x dvd b))" (is "_ = ?l") 
    unfolding Divisibility.prime_def factor_idom Units_int by auto
  from False have r: "?r = Primes.prime (nat (abs x))" (is "_ = ?r") by simp
  show ?thesis unfolding l r
  proof (intro iffI allI impI)
    fix a b
    assume prime: ?r and "x dvd a * b"
    hence "nat (abs x) dvd nat (abs a) * nat (abs b)" 
      using GCD.dvd_int_iff nat_abs_mult_distrib by auto
    from prime_dvd_mult_nat[OF prime this]
    show "x dvd a \<or> x dvd b" using GCD.dvd_int_iff by auto
  next
    assume ?l
    show "Primes.prime (nat (abs x))" unfolding Primes.prime_def
    proof (intro conjI impI allI)
      show "1 < nat (abs x)" using False by auto
      fix m
      assume dvd1: "m dvd nat (abs x)"
      hence dvd2: "int m dvd x" using int_dvd_iff by blast
      from dvd1 obtain n where prod: "nat (abs x) = m * n" unfolding dvd_def by auto
      hence "nat (abs x) dvd m * n" by auto
      hence dvd: "x dvd int m * int n" by (metis Int.dvd_int_iff of_nat_mult)
      from False prod have nz: "m \<noteq> 0" "n \<noteq> 0" by (cases m, auto, cases n, auto)
      with `?l`[rule_format, OF _ _ dvd] have "x dvd int m \<or> x dvd int n" by auto
      thus "m = 1 \<or> m = nat (abs x)"
      proof
        assume "x dvd int m"
        with dvd2 have "abs x = abs m" by (metis zdvd_antisym_abs)
        thus ?thesis by auto
      next
        assume x: "x dvd int n"
        from prod have "n dvd nat (abs x)" by auto
        hence "int n dvd x" using int_dvd_iff by blast
        with x have "abs x = abs n" by (metis zdvd_antisym_abs)
        with prod have "m = 1" using False by auto
        thus ?thesis ..
      qed
    qed
  qed
qed

lemma irreducible_int: "irreducible (x :: int) = (x = 0 \<or> Primes.prime (nat (abs x)))"
proof (cases "x = 0 \<or> x = 1 \<or> x = -1")
  case True
  thus ?thesis
    unfolding irreducible_def Units_int properfactor_def factor_idom
    by (cases "x = 1"; cases "x = 0"; cases "x = -1"; auto)
next
  case False
  from False have id: "irreducible x = (\<forall> y. properfactor y x \<longrightarrow> (y = 1 \<or> y = -1))"
    unfolding irreducible_def Units_int properfactor_def factor_idom 
    by auto
  show ?thesis unfolding id
  proof (intro iffI allI impI)
    fix y
    assume x: "x = 0 \<or> Primes.prime (nat (abs x))" and y: "properfactor y x"
    with False have x: "Primes.prime (nat (abs x))" by auto
    from False y[unfolded properfactor_def factor_idom] have dvd: "y dvd x" and ndvd: "\<not> x dvd y" 
      by (auto, cases "y = 0", auto)
    from dvd have dvd: "nat (abs y) dvd nat (abs x)" using GCD.dvd_int_iff by blast
    from ndvd have ndvd: "\<not> nat (abs x) dvd nat (abs y)" using GCD.dvd_int_iff by blast
    from dvd x[unfolded Primes.prime_def] have "nat (abs y) = 1 \<or> nat (abs y) = nat (abs x)" by auto
    with ndvd have "nat (abs y) = 1" by auto
    thus "y = 1 \<or> y = -1" by auto
  next
    assume pf: "\<forall> y. properfactor y x \<longrightarrow> y = 1 \<or> y = -1"
    have "Primes.prime (nat (abs x))" unfolding Primes.prime_def
    proof (intro conjI impI allI)
      show "1 < nat (abs x)" using False by auto
      fix m
      assume "m dvd nat (abs x)"
      hence dvd: "int m dvd x" by (simp add: int_dvd_iff)
      with pf[rule_format, of "int m", unfolded properfactor_def factor_idom] False
      have "x dvd int m \<or> int m = 1" by (auto, cases "m = 0", auto)
      thus "m = 1 \<or> m = nat (abs x)"
      proof
        assume "x dvd int m"
        with dvd have "abs x = abs (int m)" by (metis zdvd_antisym_abs)
        thus ?thesis by auto
      qed auto
    qed
    thus "x = 0 \<or> Primes.prime (nat (abs x))" ..
  qed
qed

lemma factorial_monoid_int: "factorial_monoid (mk_monoid::int monoid)"
proof -
  let ?C = "mk_monoid::int monoid"
  interpret comm_monoid_cancel ?C by (rule comm_monoid_cancel_idom)
  show ?thesis unfolding factorial_condition_one[symmetric]
  proof
    show "divisor_chain_condition_monoid ?C"
      by (unfold_locales, unfold properfactor_def factor_idom, auto,
      rule wf_subset[OF wf_measure[of "\<lambda> x. nat (abs x)"]], auto)
      (metis dvd_if_abs_eq dvd_imp_le_int le_less)
    show "primeness_condition_monoid ?C"
      by(unfold_locales, unfold prime_int irreducible_int, auto)
  qed
qed

instance by (intro_classes, rule factorial_monoid_int)
end

lemma Units_field: "(x \<in> Units (mk_monoid :: 'a :: field monoid)) = (x \<noteq> 0)"
  unfolding Units_def by (auto, intro bexI[of _ "inverse x"], auto) 

lemma prime_field: "Divisibility.prime (mk_monoid :: 'a :: field monoid) x = (x = 0)"
  unfolding Divisibility.prime_def factor_idom Units_field
  by auto

lemma irreducible_field: "irreducible (x::'a::field) = (x = 0)"
  unfolding irreducible_def properfactor_def factor_idom Units_field
  by auto

lemma factorial_monoid_field: "factorial_monoid (mk_monoid :: 'a :: field monoid)"
proof -
  let ?C = "mk_monoid::'a::field monoid"
  interpret comm_monoid_cancel ?C by (rule comm_monoid_cancel_idom)
  show ?thesis unfolding factorial_condition_one[symmetric]
  proof
    show "divisor_chain_condition_monoid ?C"
      by (unfold_locales, unfold properfactor_def factor_idom, auto,
      rule wf_subset[OF wf_measure], auto simp: field_simps dvd_field)
    show "primeness_condition_monoid ?C"
      by(unfold_locales, unfold prime_field irreducible_field, auto)
  qed
qed

instance field \<subseteq> ufd by (intro_classes, rule factorial_monoid_field)



subsection\<open>Results for GCDs etc.\<close>

lemma listprod_remove1: "(x :: 'b :: comm_monoid_mult) \<in> set xs \<Longrightarrow> listprod (remove1 x xs) * x = listprod xs"
  by (induct xs, auto simp: ac_simps)

locale ufd_loc = fixes ty :: "'a :: ufd itself" begin

abbreviation (input) "M \<equiv> mk_monoid::'a monoid"

sublocale factorial_monoid M by(rule factorial)

end

(* Isabelle 2015-style gcd-class without normalization and factors *)
class comm_ring_gcd = gcd + comm_ring_1 + 
  assumes gcd_dvd1_2015[iff]: "gcd a b dvd a"
    and   gcd_dvd2_2015 [iff]: "gcd a b dvd b"
    and   gcd_greatest_2015: "c dvd a \<Longrightarrow> c dvd b \<Longrightarrow> c dvd gcd a b"

definition ufd_gcd :: "'a :: ufd \<Rightarrow> 'a \<Rightarrow> 'a" where
  "ufd_gcd x y = (if x = 0 then y else if y = 0 then x else somegcd mk_monoid x y)"

interpretation ufd_gcd: comm_ring_gcd "1::'a::ufd" 0 "op *" ufd_gcd ufd_lcm "op +" 
  "op -" uminus
proof 
  interpret ufd_loc.
  note d = dvd.dvd_def ufd_gcd_def carrier_0
  fix a b c :: 'a
  show "dvd.dvd op * (ufd_gcd a b) a" 
  proof (cases "a = 0 \<or> b = 0")
    case True
    thus ?thesis unfolding d by auto
  next
    case False
    with gcd_divides_l[of a b]
    show ?thesis unfolding d by (auto simp: factor_def)
  qed
  show "dvd.dvd op * (ufd_gcd a b) b" 
  proof (cases "a = 0 \<or> b = 0")
    case True
    thus ?thesis unfolding d by auto
  next
    case False
    with gcd_divides_r[of a b]
    show ?thesis unfolding d by (auto simp: factor_def)
  qed
  assume dvd: "dvd.dvd op * c a" "dvd.dvd op * c b"
  show "dvd.dvd op * c (ufd_gcd a b)"
  proof (cases "a = 0 \<or> b = 0 \<or> c = 0")
    case True
    thus ?thesis using dvd unfolding d by (auto simp: factor_def)
  next
    case False
    hence abc: "a \<noteq> 0" "b \<noteq> 0" "c \<noteq> 0" by auto
    with dvd have "factor c a" "factor c b" unfolding d by (auto simp: factor_def)
    from gcd_divides[OF this, unfolded d, OF abc]
    show ?thesis using abc unfolding d by (auto simp: factor_def)
  qed
qed

lemma ufd_gcd_dvd1 [iff]: "ufd_gcd a b dvd a"
    and ufd_gcd_dvd2 [iff]: "ufd_gcd a b dvd b"
    and ufd_gcd_greatest: "c dvd a \<Longrightarrow> c dvd b \<Longrightarrow> c dvd ufd_gcd a b"
  using ufd_gcd.gcd_dvd1_2015[of a b] ufd_gcd.gcd_dvd2_2015[of a b] ufd_gcd.gcd_greatest_2015[of c a b]
  unfolding dvd.dvd_def dvd_def by blast+

lemma ufd_gcd_greatest_mult: assumes "c dvd a * d" "c dvd b * d"
  shows "c dvd ufd_gcd a b * d"
proof (cases "a = 0 \<or> b = 0 \<or> d = 0")
  interpret ufd_loc.
  case False
  from ufd_gcd_greatest[OF assms] have c: "c dvd ufd_gcd (d * a) (d * b)" by (auto simp: ac_simps)
  from gcd_mult[of a b d] False have "associated M (d * ufd_gcd a b) (ufd_gcd (d * a) (d * b))"
    unfolding ufd_gcd_def by auto
  from this[unfolded associated_def] have "ufd_gcd (d * a) (d * b) dvd ufd_gcd a b * d"
    by (auto simp: ac_simps)
  from dvd_trans[OF c this] show ?thesis .
next
  case True
  thus ?thesis using assms unfolding ufd_gcd_def by auto
qed

definition listgcd :: "'a::ufd list \<Rightarrow> 'a" where
  "listgcd xs = foldr ufd_gcd xs 0"

lemma listgcd_simps: "listgcd [] = 0" "listgcd (x # xs) = ufd_gcd x (listgcd xs)"
  by (auto simp: listgcd_def)

lemma listgcd: "x \<in> set xs \<Longrightarrow> listgcd xs dvd x" 
proof (induct xs)
  case (Cons y ys)
  show ?case
  proof (cases "x = y")
    case False
    with Cons have dvd: "listgcd ys dvd x" by auto
    thus ?thesis unfolding listgcd_simps using dvd_trans by blast
  next
    case True
    thus ?thesis unfolding listgcd_simps using dvd_trans by blast
  qed
qed simp

lemma listgcd_greatest_mult: "(\<And> x. x \<in> set xs \<Longrightarrow> y dvd x * z) \<Longrightarrow> y dvd listgcd xs * z"
proof (induct xs)
  case (Cons x xs)
  from Cons have "y dvd x * z" "y dvd listgcd xs * z" by auto
  thus ?case unfolding listgcd_simps by (rule ufd_gcd_greatest_mult)
qed (simp add: listgcd_simps)

lemma listgcd_greatest: "(\<And> x. x \<in> set xs \<Longrightarrow> y dvd x) \<Longrightarrow> y dvd listgcd xs"
  using listgcd_greatest_mult[of xs y 1] by (metis mult.right_neutral)

definition divides_ff :: "'b::idom fract \<Rightarrow> 'b fract \<Rightarrow> bool"
  where "divides_ff x y = (\<exists> r. y = embed_ff r * x)" 

lemma ff_list_pairs: 
  "\<exists> xs. X = map (\<lambda> (x,y). Fraction_Field.Fract x y) xs \<and> 0 \<notin> snd ` set xs"
proof (induct X)
  case (Cons a X)
  from Cons(1) obtain xs where X: "X = map (\<lambda> (x,y). Fraction_Field.Fract x y)  xs" and xs: "0 \<notin> snd ` set xs"
    by auto
  obtain x y where a: "a = Fraction_Field.Fract x y" and y: "y \<noteq> 0" by (cases a, auto)
  show ?case unfolding X a using xs y
    by (intro exI[of _ "(x,y) # xs"], auto)
qed auto

lemma divides_dvd_embed_ff[simp]: "divides_ff (embed_ff x) (embed_ff y) = (x dvd y)"
  unfolding divides_ff_def dvd_def
  by (simp add: embed_ff_def eq_fract(1) mult.commute)

lemma divides_ff_mult: "divides_ff x y \<Longrightarrow> divides_ff (z * x) (z * y)"
  unfolding divides_ff_def by auto

lemma divides_ff_mult_inv: "divides_ff (z * x) (z * y) \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> divides_ff x y"
  unfolding divides_ff_def by auto

definition gcd_ff_list :: "'a::ufd fract list \<Rightarrow> 'a fract \<Rightarrow> bool" where
  "gcd_ff_list X g = (
     (\<forall> x \<in> set X. divides_ff g x) \<and> 
     (\<forall> d. (\<forall> x \<in> set X. divides_ff d x) \<longrightarrow> divides_ff d g))"

interpretation embed_ff: inj_ring_hom embed_ff by (rule embed_ff)

lemma gcd_ff_list_exists: "\<exists> g. gcd_ff_list (X :: 'a::ufd fract list) g"
proof -
  from ff_list_pairs[of X] obtain xs where X: "X = map (\<lambda> (x,y). Fraction_Field.Fract x y) xs"
    and xs: "0 \<notin> snd ` set xs" by auto
  def r \<equiv> "listprod (map snd xs)"
  have r: "r \<noteq> 0" unfolding r_def listprod_zero_iff using xs by auto
  def ys \<equiv> "map (\<lambda> (x,y). x * listprod (remove1 y (map snd xs))) xs"
  {
    fix i
    assume "i < length X"
    hence i: "i < length xs" unfolding X by auto
    obtain x y where xsi: "xs ! i = (x,y)" by force
    with i have "(x,y) \<in> set xs" unfolding set_conv_nth by force
    hence y_mem: "y \<in> set (map snd xs)" by force
    with xs have y: "y \<noteq> 0" by force
    from i have id1: "ys ! i = x * listprod (remove1 y (map snd xs))" unfolding ys_def using xsi by auto
    from i xsi have id2: "X ! i = Fraction_Field.Fract x y" unfolding X by auto
    have lp: "listprod (remove1 y (map snd xs)) * y = r" unfolding r_def
      by (rule listprod_remove1[OF y_mem])
    have "ys ! i \<in> set ys" using i unfolding ys_def by auto
    moreover have "embed_ff (ys ! i) = embed_ff r * (X ! i)"
      unfolding id1 id2 embed_ff_def mult_fract
      by (subst eq_fract(1), force, force simp: y, simp add: lp)
    ultimately have "ys ! i \<in> set ys" "embed_ff (ys ! i) = embed_ff r * (X ! i)" .
  } note ys = this
  def G \<equiv> "listgcd ys"
  def g \<equiv> "embed_ff G * Fraction_Field.Fract 1 r"
  have len: "length X = length ys" unfolding X ys_def by auto
  show ?thesis
  proof (rule exI[of _ g], unfold gcd_ff_list_def, intro ballI conjI impI allI)
    fix x
    assume "x \<in> set X"
    then obtain i where i: "i < length X" and x: "x = X ! i" unfolding set_conv_nth by auto
    from ys[OF i] have id: "embed_ff (ys ! i) = embed_ff r * x" 
      and ysi: "ys ! i \<in> set ys" unfolding x by auto
    from listgcd[OF ysi] have "G dvd ys ! i" unfolding G_def .
    then obtain d where ysi: "ys ! i = G * d" unfolding dvd_def by auto
    have "embed_ff d * (embed_ff G * Fraction_Field.Fract 1 r) = x * (embed_ff r * Fraction_Field.Fract 1 r)" 
      using id[unfolded ysi]
      by (simp add: ac_simps)
    also have "\<dots> = x" using r unfolding embed_ff_def by (simp add: eq_fract One_fract_def)
    finally have "embed_ff d * (embed_ff G * Fraction_Field.Fract 1 r) = x" by simp
    thus "divides_ff g x" unfolding divides_ff_def g_def 
      by (intro exI[of _ d], auto)
  next
    fix d
    assume "Ball (set X) (divides_ff d)"
    hence "Ball ((\<lambda> x. embed_ff r * x) ` set X) (divides_ff (embed_ff r * d))"
      using divides_ff_mult[of _ _ "embed_ff r"]
      by (induct X, auto)
    also have "(\<lambda> x. embed_ff r * x) ` set X = embed_ff ` set ys"
      unfolding set_conv_nth using ys len by force
    finally have dvd: "Ball (set ys) (\<lambda> y. divides_ff (embed_ff r * d) (embed_ff y))" by auto
    obtain nd dd where d: "d = Fraction_Field.Fract nd dd" and dd: "dd \<noteq> 0" by (cases d, auto)
    {
      fix y
      assume "y \<in> set ys"
      hence "divides_ff (embed_ff r * d) (embed_ff y)" using dvd by auto
      from this[unfolded divides_ff_def d embed_ff_def mult_fract]
      obtain ra where "Fraction_Field.Fract y 1 = Fraction_Field.Fract (ra * (r * nd)) dd" by auto
      hence "y * dd = ra * (r * nd)" by (simp add: eq_fract dd)
      hence "r * nd dvd y * dd" by auto
    }
    hence "r * nd dvd listgcd ys * dd" by (rule listgcd_greatest_mult)
    hence "divides_ff (embed_ff r * d) (embed_ff G)" unfolding embed_ff_def d mult_fract
      G_def divides_ff_def by (auto simp add: eq_fract dd dvd_def)
    also have "embed_ff G = embed_ff r * g" unfolding g_def using r
      by (auto simp: embed_ff_def eq_fract)
    finally show "divides_ff d g" 
      by (rule divides_ff_mult_inv, insert r, auto simp: embed_ff_def Zero_fract_def eq_fract)
  qed
qed

definition some_gcd_ff_list :: "'a :: ufd fract list \<Rightarrow> 'a fract" where
  "some_gcd_ff_list xs = (SOME g. gcd_ff_list xs g)"

lemma some_gcd_ff_list: "gcd_ff_list xs (some_gcd_ff_list xs)"
  unfolding some_gcd_ff_list_def using gcd_ff_list_exists[of xs]
  by (rule someI_ex)

lemma some_gcd_ff_list_divides: "x \<in> set xs \<Longrightarrow> divides_ff (some_gcd_ff_list xs) x"
  using some_gcd_ff_list[of xs] unfolding gcd_ff_list_def by auto

lemma some_gcd_ff_list_greatest: "Ball (set xs) (divides_ff d) \<Longrightarrow> divides_ff d (some_gcd_ff_list xs)"
  using some_gcd_ff_list[of xs] unfolding gcd_ff_list_def by auto

lemma divides_ff_refl[simp]: "divides_ff x x"
  unfolding divides_ff_def
  by (rule exI[of _ 1], auto simp: embed_ff_def One_fract_def)

lemma divides_ff_trans:
  "divides_ff x y \<Longrightarrow> divides_ff y z \<Longrightarrow> divides_ff x z"
  unfolding divides_ff_def
  by (auto simp del: embed_ff.hom_mult simp add: embed_ff.hom_mult[symmetric])

lemma divides_ff_mult_right: "a \<noteq> 0 \<Longrightarrow> divides_ff (x * inverse a) y \<Longrightarrow> divides_ff x (a * y)"
  unfolding divides_ff_def divide_inverse[symmetric] by auto

definition eq_dff :: "'a :: ufd fract \<Rightarrow> 'a fract \<Rightarrow> bool" (infix "=dff" 50) where
  "x =dff y \<longleftrightarrow> divides_ff x y \<and> divides_ff y x"

lemma eq_dffI[intro]: "divides_ff x y \<Longrightarrow> divides_ff y x \<Longrightarrow> x =dff y" 
  unfolding eq_dff_def by auto

lemma eq_dff_refl[simp]: "x =dff x"
  by (intro eq_dffI, auto)

lemma eq_dff_sym: "x =dff y \<Longrightarrow> y =dff x" unfolding eq_dff_def by auto

lemma eq_dff_trans[trans]: "x =dff y \<Longrightarrow> y =dff z \<Longrightarrow> x =dff z"
  unfolding eq_dff_def using divides_ff_trans by auto

lemma eq_dff_mult_right_cong: "y =dff z \<Longrightarrow> x * y =dff x * z" 
  unfolding eq_dff_def using divides_ff_mult[of y z x] divides_ff_mult[of z y x] by auto

lemma eq_dff_mult_right_trans[trans]: "x =dff y * z \<Longrightarrow> z =dff u \<Longrightarrow> x =dff y * u"
  using eq_dff_mult_right_cong eq_dff_trans by blast

lemma some_gcd_ff_list_smult: "a \<noteq> 0 \<Longrightarrow> some_gcd_ff_list (map (op * a) xs) =dff a * some_gcd_ff_list xs"
proof 
  let ?g = "some_gcd_ff_list (map (op * a) xs)"
  show "divides_ff (a * some_gcd_ff_list xs) ?g"
    by (rule some_gcd_ff_list_greatest, insert some_gcd_ff_list_divides[of _ xs], auto simp: divides_ff_def)
  assume a: "a \<noteq> 0"
  show "divides_ff ?g (a * some_gcd_ff_list xs)"
  proof (rule divides_ff_mult_right[OF a some_gcd_ff_list_greatest], intro ballI)
    fix x
    assume x: "x \<in> set xs"
    have "divides_ff (?g * inverse a) x = divides_ff (inverse a * ?g) (inverse a * (a * x))"
      using a by (simp add: field_simps)
    also have "\<dots>"
      by (rule divides_ff_mult, rule some_gcd_ff_list_divides, insert x, auto)
    finally show "divides_ff (?g * inverse a) x" .
  qed
qed

end
