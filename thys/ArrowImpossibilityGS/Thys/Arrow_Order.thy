(*  Author:     Tobias Nipkow, 2007  *)

section "Arrow's Theorem for Strict Linear Orders"

theory Arrow_Order imports Main "~~/src/HOL/Library/FuncSet"
begin

text{* This theory formalizes the third proof due to
Geanakoplos~\cite{Geanakoplos05}.  Preferences are modeled as strict
linear orderings. The set of alternatives need not be finite.

Individuals are assumed to be finite but are not a priori identified with an
initial segment of the naturals. In retrospect this generality appears
gratuitous and complicates some of the low-level reasoning where we use a
bijection with such an initial segment.  *}

typedecl alt
typedecl indi

abbreviation "I == (UNIV::indi set)"

axiomatization where
  alt3: "\<exists>a b c::alt. distinct[a,b,c]" and
  finite_indi: "finite I"

abbreviation "N == card I"

lemma third_alt: "a \<noteq> b \<Longrightarrow> \<exists>c::alt. distinct[a,b,c]"
using alt3 by simp metis

lemma alt2: "\<exists>b::alt. b \<noteq> a"
using alt3 by simp metis

type_synonym pref = "(alt * alt)set"

definition "Lin == {L::pref. strict_linear_order L}"

lemmas slo_defs = Lin_def strict_linear_order_on_def total_on_def irrefl_def

lemma notin_Lin_iff: "L : Lin \<Longrightarrow> x\<noteq>y \<Longrightarrow> (x,y) \<notin> L \<longleftrightarrow> (y,x) : L"
apply(auto simp add: slo_defs)
apply(metis trans_def)
done

lemma converse_in_Lin[simp]: "L\<inverse> : Lin \<longleftrightarrow> L : Lin"
apply (simp add: slo_defs)
apply blast
done

lemma Lin_irrefl: "L:Lin \<Longrightarrow> (a,b):L \<Longrightarrow> (b,a):L \<Longrightarrow> False"
by(simp add:slo_defs)(metis trans_def)

corollary linear_alt: "\<exists>L::pref. L : Lin"
using well_order_on[where 'a = "alt", of UNIV]
apply (auto simp:well_order_on_def Lin_def)
apply (metis strict_linear_order_on_diff_Id)
done

abbreviation
 rem :: "pref \<Rightarrow> alt \<Rightarrow> pref" where
"rem L a \<equiv> {(x,y). (x,y) \<in> L \<and> x\<noteq>a \<and> y\<noteq>a}"
definition
 mktop :: "pref \<Rightarrow> alt \<Rightarrow> pref" where
"mktop L b \<equiv> rem L b \<union> {(x,b)|x. x\<noteq>b}"
definition
 mkbot :: "pref \<Rightarrow> alt \<Rightarrow> pref" where
"mkbot L b \<equiv> rem L b \<union> {(b,y)|y. y\<noteq>b}"
definition
 below :: "pref \<Rightarrow> alt \<Rightarrow> alt \<Rightarrow> pref" where
"below L a b \<equiv> rem L a \<union>
  {(a,b)} \<union> {(x,a)|x. (x,b) : L \<and> x\<noteq>a} \<union> {(a,y)|y. (b,y) : L \<and> y\<noteq>a}"
definition
 above :: "pref \<Rightarrow> alt \<Rightarrow> alt \<Rightarrow> pref" where
"above L a b \<equiv> rem L b \<union>
  {(a,b)} \<union> {(x,b)|x. (x,a) : L \<and> x\<noteq>b} \<union> {(b,y)|y. (a,y) : L \<and> y\<noteq>b}"

lemma in_mktop: "(x,y) \<in> mktop L z \<longleftrightarrow> x\<noteq>z \<and> (if y=z then x\<noteq>y else (x,y) \<in> L)"
by(auto simp:mktop_def)

lemma in_mkbot: "(x,y) \<in> mkbot L z \<longleftrightarrow> y\<noteq>z \<and> (if x=z then x\<noteq>y else (x,y) \<in> L)"
by(auto simp:mkbot_def)

lemma in_above: "a\<noteq>b \<Longrightarrow> L:Lin \<Longrightarrow>
  (x,y) : above L a b \<longleftrightarrow> x\<noteq>y \<and>
  (if x=b then (a,y) : L else
   if y=b then x=a | (x,a) : L else (x,y) : L)"
by(auto simp:above_def slo_defs)

lemma in_below: "a\<noteq>b \<Longrightarrow> L:Lin \<Longrightarrow>
  (x,y) : below L a b \<longleftrightarrow> x\<noteq>y \<and>
  (if y=a then (x,b) : L else
   if x=a then y=b | (b,y) : L else (x,y) : L)"
by(auto simp:below_def slo_defs)

declare [[simp_depth_limit = 2]]

lemma mktop_Lin: "L : Lin \<Longrightarrow> mktop L x : Lin"
by(auto simp add:slo_defs mktop_def trans_def)
lemma mkbot_Lin: "L : Lin \<Longrightarrow> mkbot L x : Lin"
by(auto simp add:slo_defs trans_def mkbot_def)

lemma below_Lin: "x\<noteq>y \<Longrightarrow> L : Lin \<Longrightarrow> below L x y : Lin"
unfolding slo_defs below_def trans_def
apply(simp)
apply blast
done

lemma above_Lin: "x\<noteq>y \<Longrightarrow> L : Lin \<Longrightarrow> above L x y : Lin"
unfolding slo_defs above_def trans_def
apply(simp)
apply blast
done

declare [[simp_depth_limit = 50]]

abbreviation lessLin :: "alt \<Rightarrow> pref \<Rightarrow> alt \<Rightarrow> bool" ("(_ <\<^bsub>_\<^esub> _)" [51, 51] 50)
where "a <\<^bsub>L\<^esub> b == (a,b) : L"

definition "Prof = I \<rightarrow> Lin"

abbreviation "SWF == Prof \<rightarrow> Lin"

definition "unanimity F == \<forall>P\<in>Prof.\<forall>a b. (\<forall>i. a <\<^bsub>P i\<^esub> b) \<longrightarrow>  a <\<^bsub>F P\<^esub> b"

definition "IIA F == \<forall>P\<in>Prof.\<forall>P'\<in>Prof.\<forall>a b.
   (\<forall>i. a <\<^bsub>P i\<^esub> b \<longleftrightarrow> a <\<^bsub>P' i\<^esub> b) \<longrightarrow> (a <\<^bsub>F P\<^esub> b \<longleftrightarrow> a <\<^bsub>F P'\<^esub> b)"

definition "dictator F i == \<forall>P\<in>Prof. F P = P i"

lemma dictatorI: "F : SWF \<Longrightarrow>
  \<forall>P\<in>Prof. \<forall>a b. a \<noteq> b \<longrightarrow> (a,b) : P i \<longrightarrow> (a,b) : F P \<Longrightarrow> dictator F i"
apply(simp add:dictator_def Prof_def Pi_def Lin_def strict_linear_order_on_def)
apply safe
 apply(erule_tac x=P in allE)
 apply(erule_tac x=P in allE)
 apply(simp add:total_on_def irrefl_def)
 apply (metis trans_def)
apply (metis irrefl_def)
done

lemma const_Lin_Prof: "L:Lin \<Longrightarrow> (%p. L) : Prof"
by(simp add:Prof_def Pi_def)

lemma complete_Lin: assumes "a\<noteq>b" shows "EX L:Lin. (a,b) : L"
proof -
  from linear_alt obtain R where "R:Lin" by auto
  thus ?thesis by (metis assms in_mkbot mkbot_Lin)
qed

declare Let_def[simp]

theorem Arrow: assumes "F : SWF" and u: "unanimity F" and "IIA F"
shows "EX i. dictator F i"
proof -
  { fix a b a' b' and P P'
    assume d1: "a\<noteq>b" "a'\<noteq>b'" and d2: "a\<noteq>b'" "b\<noteq>a'" and
      "P : Prof" "P' : Prof" and 1: "\<forall>i. (a,b) : P i \<longleftrightarrow> (a',b') : P' i"
    assume "(a,b) : F P"
    def Q \<equiv> "%i. let L = (if a=a' then P i else below (P i) a' a)
                  in if b=b' then L else above L b b'"
    have "Q : Prof" using `P : Prof`
      by(simp add:Q_def Prof_def Pi_def above_Lin below_Lin)
    hence "F Q : Lin" using `F : SWF` by(simp add:Pi_def)
    have "\<forall>i. (a,b) : P i \<longleftrightarrow> (a,b) : Q i" using d1 d2 `P : Prof`
      by(simp add:in_above in_below Q_def Prof_def Pi_def below_Lin)
    hence "(a,b) : F Q" using `(a,b) : F P` `IIA F` `P:Prof` `Q : Prof`
      unfolding IIA_def by blast
    moreover
    { assume "a\<noteq>a'"
      hence "!!i. (a',a) : Q i" using d1 d2 `P : Prof`
        by(simp add:in_above in_below Q_def Prof_def Pi_def below_Lin)
      hence "(a',a) : F Q" using u `Q : Prof` by(simp add:unanimity_def)
    } moreover
    { assume "b\<noteq>b'"
      hence "!!i. (b,b') : Q i" using d1 d2 `P : Prof`
        by(simp add:in_above in_below Q_def Prof_def Pi_def below_Lin)
      hence "(b,b') : F Q" using u `Q : Prof` by(simp add:unanimity_def)
    }
    ultimately have "(a',b') : F Q" using `F Q : Lin`
      unfolding slo_defs trans_def 
      by safe metis
    moreover
    have "\<forall>i. (a',b') : Q i \<longleftrightarrow> (a',b') : P' i" using d1 d2 `P : Prof` 1
      by(simp add:Q_def in_below in_above Prof_def Pi_def below_Lin) blast
    ultimately have "(a',b') : F P'"
      using `IIA F` `P' : Prof` `Q : Prof` unfolding IIA_def by blast
  } note 1 = this
  { fix a b a' b' and P P'
    assume "a\<noteq>b" "a'\<noteq>b'" "a\<noteq>b'" "b\<noteq>a'" "P : Prof" "P' : Prof"
           "\<forall>i. (a,b) : P i \<longleftrightarrow> (a',b') : P' i"
    hence "(a,b) : F P \<longleftrightarrow> (a',b') : F P'" using 1 by blast
  } note 2 = this
  { fix a b P P'
    assume "a\<noteq>b" "P : Prof" "P' : Prof" and
      iff: "\<forall>i. (a,b) : P i \<longleftrightarrow> (b,a) : P' i"
    from `a\<noteq>b` obtain c where dist: "distinct[a,b,c]" using third_alt by metis
    let ?Q = "%p. below (P p) c b"
    let ?R = "%p. below (?Q p) b a"
    let ?S = "%p. below (?R p) a c"
    have "?Q : Prof" using `P : Prof` dist
      by(auto simp add:Prof_def Pi_def below_Lin)
    hence "?R : Prof" using dist by(auto simp add:Prof_def Pi_def below_Lin)
    hence "?S : Prof" using dist by(auto simp add:Prof_def Pi_def below_Lin)
    have "\<forall>i. (a,b) : P i \<longleftrightarrow> (a,c) : ?Q i" using `P : Prof` dist
      by(auto simp add:in_below Prof_def Pi_def)
    hence ab: "(a,b) : F P \<longleftrightarrow> (a,c) : F ?Q"
      using 2 `P : Prof` `?Q : Prof` dist[simplified] by (blast)
    have "\<forall>i. (a,c) : ?Q i \<longleftrightarrow> (b,c) : ?R i" using `P : Prof` dist
      by(auto simp add:in_below Prof_def Pi_def below_Lin)
    hence ac: "(a,c) : F ?Q \<longleftrightarrow> (b,c) : F ?R"
      using 2 `?Q : Prof` `?R : Prof` dist[simplified] by (blast)
    have "\<forall>i. (b,c) : ?R i \<longleftrightarrow> (b,a) : ?S i" using `P : Prof` dist
      by(auto simp add:in_below Prof_def Pi_def below_Lin)
    hence bc: "(b,c) : F ?R \<longleftrightarrow> (b,a) : F ?S"
      using `?R : Prof` `?S : Prof` dist[simplified] 2
      apply -
      apply(rule 2)
      by fast+
    have "\<forall>i. (b,a) : ?S i \<longleftrightarrow> (a,b) : P i" using `P : Prof` dist
      by(auto simp add:in_below Prof_def Pi_def below_Lin)
    hence "\<forall>i. (b,a) : ?S i \<longleftrightarrow> (b,a) : P' i" using iff by blast
    hence ba: "(b,a) : F ?S \<longleftrightarrow> (b,a) : F P'"
      using `IIA F` `P' : Prof` `?S : Prof` unfolding IIA_def by fast
    from ab ac bc ba have "(a,b) : F P \<longleftrightarrow> (b,a) : F P'" by simp
  } note 3 = this
  { fix a b c P P'
    assume A: "a\<noteq>b" "b\<noteq>c" "a\<noteq>c" "P : Prof" "P' : Prof" and
      iff: "\<forall>i. (a,b) : P i \<longleftrightarrow> (b,c) : P' i"
    hence "\<forall>i. (b,a) : (converse o P)i \<longleftrightarrow> (b,c) : P' i" by simp
    moreover have cP: "converse o P : Prof"
      using `P:Prof` by(simp add:Prof_def Pi_def)
    ultimately have "(b,a) : F(converse o P) \<longleftrightarrow> (b,c) : F P'" using A 2
      by metis
    moreover have "(a,b) : F P \<longleftrightarrow> (b,a) : F(converse o P)"
      by (rule 3[OF `a\<noteq>b` `P:Prof` cP]) simp
    ultimately have "(a,b) : F P \<longleftrightarrow> (b,c) : F P'" by blast
  } note 4 = this
  { fix a b a' b' :: alt and P P'
    assume A: "a\<noteq>b" "a'\<noteq>b'" "P : Prof" "P' : Prof"
      "\<forall>i. (a,b) : P i \<longleftrightarrow> (a',b') : P' i"
    have "(a,b) : F P \<longleftrightarrow> (a',b') : F P'"
    proof-
      { assume "a\<noteq>b' & b\<noteq>a'" hence ?thesis using 2 A by blast }
      moreover
      { assume "a=b' & b\<noteq>a'" hence ?thesis using 4 A by blast }
      moreover
      { assume "a\<noteq>b' & b=a'" hence ?thesis using 4 A by blast }
      moreover
      { assume "a=b' & b=a'" hence ?thesis using 3 A by blast }
      ultimately show ?thesis by blast
    qed
  } note pairwise_neutrality = this
  obtain h :: "indi \<Rightarrow> nat" where
    injh: "inj h" and surjh: "h ` I = {0..<N}"
    by(metis ex_bij_betw_finite_nat[OF finite_indi] bij_betw_def)
  obtain a b :: alt where "a \<noteq> b" using alt3 by auto
  obtain Lab where "(a,b) : Lab" "Lab:Lin" using `a\<noteq>b` by (metis complete_Lin)
  hence "(b,a) \<notin> Lab" by(simp add:slo_defs trans_def) metis
  obtain Lba where "(b,a) : Lba" "Lba:Lin" using `a\<noteq>b` by (metis complete_Lin)
  hence "(a,b) \<notin> Lba" by(simp add:slo_defs trans_def) metis
  let ?Pi = "%n. %i. if h i < n then Lab else Lba"
  have PiProf: "!!n. ?Pi n : Prof" using `Lab:Lin` `Lba:Lin`
    unfolding Prof_def Pi_def by simp
  have "EX n<N. (\<forall>m\<le>n. (b,a) : F(?Pi m)) & (a,b) : F(?Pi(n+1))"
  proof -
    have 0: "!!n. F(?Pi n) : Lin" using `F : SWF` PiProf by(simp add:Pi_def)
    have "F(%i. Lba):Lin" using `F:SWF` `Lba:Lin` by(simp add:Prof_def Pi_def)
    hence 1: "(a,b) \<notin> F(?Pi 0)" using u `(a,b) \<notin> Lba` `Lba:Lin` `Lba:Lin` `a\<noteq>b`
      by(simp add:unanimity_def notin_Lin_iff const_Lin_Prof)
    have "?Pi N = (%p. Lab)" using surjh [THEN equalityD1]
      by(auto simp: subset_eq)
    moreover
    have "F(%i. Lab):Lin" using `F:SWF` `Lab:Lin` by(simp add:Prof_def Pi_def)
    ultimately have 2: "(a,b) \<in> F(?Pi N)" using u `(a,b) : Lab` `Lab:Lin`
      by(simp add:unanimity_def const_Lin_Prof)
    with ex_least_nat_less[of "%n. (a,b) : F(?Pi n)",OF 1 2]
      notin_Lin_iff[OF 0 `a\<noteq>b`]
    show ?thesis by simp
  qed
  then obtain n where n: "n<N" "\<forall>m\<le>n. (b,a) : F(?Pi m)" "(a,b) : F(?Pi(n+1))"
    by blast
  have "dictator F (inv h n)"
  proof (rule dictatorI [OF `F : SWF`], auto)
    fix P c d assume "P \<in> Prof" "c\<noteq>d" "(c,d) \<in> P(inv h n)"
    then obtain e where dist: "distinct[c,d,e]" using third_alt by metis
    let ?W = "%i. if h i < n then mktop (P i) e else
                  if h i = n then above (P i) c e else mkbot (P i) e"
    have "?W : Prof" using `P : Prof` dist
      by(simp add:Pi_def Prof_def mkbot_Lin mktop_Lin above_Lin)
    have "\<forall>i. (c,d) : P i \<longleftrightarrow> (c,d) : ?W i" using dist `P : Prof`
      by(auto simp: in_above in_mkbot in_mktop Prof_def Pi_def)
    hence PW: "(c,d) : F P \<longleftrightarrow> (c,d) : F ?W"
      using `IIA F`[unfolded IIA_def] `P:Prof` `?W:Prof` by fast
    have "\<forall>i. (c,e) : ?W i \<longleftrightarrow> (a,b) : ?Pi (n+1) i" using dist `P : Prof`
      by (auto simp: `(a,b):Lab` `(a,b)\<notin>Lba`
        in_mkbot in_mktop in_above Prof_def Pi_def)
    hence "(c,e) : F ?W \<longleftrightarrow> (a,b) : F(?Pi(n+1))"
      using pairwise_neutrality[of c e a b ?W "?Pi(n+1)"]
        `a\<noteq>b` dist `?W : Prof` PiProf by simp
    hence "(c,e) : F ?W" using n(3) by blast
    have "\<forall>i. (e,d) : ?W i \<longleftrightarrow> (b,a) : ?Pi n i"
      using dist `P : Prof` `(c,d) \<in> P(inv h n)` `inj h`
      by(auto simp: `(b,a):Lba` `(b,a)\<notin>Lab`
        in_mkbot in_mktop in_above Prof_def Pi_def)
    hence "(e,d) : F ?W \<longleftrightarrow> (b,a) : F(?Pi n)"
      using pairwise_neutrality[of e d b a ?W "?Pi n"]
        `a\<noteq>b` dist `?W : Prof` PiProf by simp blast
    hence "(e,d) : F ?W" using n(2) by auto
    with `(c,e) : F ?W` `?W : Prof` `F:SWF`
    have "(c,d) \<in> F ?W" unfolding Pi_def slo_defs trans_def by blast
    thus "(c,d) \<in> F P" using PW by blast
  qed
  thus ?thesis ..
qed

end
