theory "FMap-HOLCF"
  imports FMap "HOLCF-Join" "HOLCF-Set"
begin

default_sort type

subsubsection {* A partial order on finite maps *}

instantiation fmap :: (type, po) po
begin
  definition "(a::'a f\<rightharpoonup> 'b) \<sqsubseteq> b \<equiv> (fdom a = fdom b) \<and> (\<forall>x \<in> fdom a. a f! x \<sqsubseteq> b f! x)"

instance
proof default
  fix x :: "'a f\<rightharpoonup> 'b"
  show "x \<sqsubseteq> x" by (auto simp add:below_fmap_def)
next
  fix x y z :: "'a f\<rightharpoonup> 'b"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> z"
  thus "x \<sqsubseteq> z"
  apply (auto simp add: below_fmap_def)
  by (metis rev_below_trans)
next
  fix x y :: "'a f\<rightharpoonup> 'b"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> x"
  thus "x = y"
  by (metis "FMap-HOLCF.below_fmap_def" fmap_eqI po_eq_conv)
qed
end

lemma fmap_belowI:
  assumes "fdom a = fdom b"
    and "\<And> x. \<lbrakk>
      x \<in> fdom a;
      x \<in> fdom b
      \<rbrakk>  \<Longrightarrow> a f! x \<sqsubseteq> b f! x"
  shows "a \<sqsubseteq> b"
  using assms
  by (metis below_fmap_def)

lemma fmap_belowE:
  assumes "m1 \<sqsubseteq> m2"
  shows "m1 f! x \<sqsubseteq> m2 f! x"
  apply (cases "x \<in> fdom m1")
  using assms
  apply (metis below_fmap_def)
  using assms unfolding below_fmap_def
  apply (transfer, auto)
  done

subsubsection {* The order is chain-complete *}

definition fmap_lub_raw where
  "fmap_lub_raw S = (\<lambda> x. 
      if (x \<in> dom (S 0))
      then Some (\<Squnion>i::nat. the (S i x))
      else None)"

lemma fmap_lub_raw_dom[simp]: "dom (fmap_lub_raw S) = dom (S 0)"
  by (auto simp add: fmap_lub_raw_def dom_def)  

lift_definition fmap_lub :: "(nat \<Rightarrow> ('key f\<rightharpoonup> 'value::po)) \<Rightarrow> 'key f\<rightharpoonup> 'value" is "fmap_lub_raw"
  unfolding Lifting.invariant_def
  apply auto
  apply (erule  meta_allE[of _ 0])
  apply auto[1]
  apply (subgoal_tac "fun1 = fun2")
  apply auto
  done

lemma fmap_below_dom:
  "a \<sqsubseteq> b \<Longrightarrow> fdom a = fdom b"
  unfolding below_fmap_def by simp

lemma is_lub_fmap:
  assumes "chain (S::nat => 'a f\<rightharpoonup> 'b::cpo)"
  shows "range S <<| fmap_lub S"
proof(rule is_lubI)

  def d \<equiv> "fdom (S 0)"
  have [simp]:"\<And>i . fdom (S i) = d"
    using chain_mono[OF `chain S`, of 0]
    unfolding d_def
    by (metis fmap_below_dom le0)
  hence [simp]: "fdom (fmap_lub S) = d"
    unfolding fmap_lub.rep_eq fdom.rep_eq fmap_lub_raw_def  dom_def
    by auto

{
  show "range S <| fmap_lub S"
  proof(rule is_ubI)
  case (goal1 m)
    then obtain i where "m = S i" by auto
    hence "S 0 \<sqsubseteq> m" using chain_mono[OF `chain S`] by auto

    have [simp]: "fdom m = d" using `m = S i` by simp

    show "m \<sqsubseteq> fmap_lub S"
    proof(rule fmap_belowI)
      fix x
      assume "x \<in> fdom m"
      hence c2: "chain (\<lambda> i. the (Rep_fmap (S i) x))" using `chain S`
        unfolding chain_def below_fmap_def lookup.rep_eq
        by auto            

      have "m f! x = the (Rep_fmap (S i) x)"  using `m = _` by (auto simp add: lookup.rep_eq)
      hence ylt: "m f! x \<sqsubseteq> (\<Squnion>i::nat. the (Rep_fmap (S i) x))" 
          using is_ub_thelub[OF c2] by (auto simp add: lookup.rep_eq)
      also
      have "x \<in> fdom (S 0) " using `x \<in> fdom m` by simp
      hence "(\<Squnion>i::nat. the (Rep_fmap (S i) x)) = (fmap_lub S) f! x"
        by (auto simp add: fmap_lub.rep_eq lookup.rep_eq fmap_lub_raw_def fdom.rep_eq)        
      finally
      show "m f! x \<sqsubseteq> (fmap_lub S) f! x".
    qed simp
  qed
next
  fix u
  assume "range S <| u"

  hence [simp]: "fdom u = d"
    by (metis ub_rangeD  `\<And>i. fdom (S i) = d` fmap_below_dom)

  show "fmap_lub S \<sqsubseteq> u "
  proof(rule fmap_belowI)
    fix x

    assume  "x \<in> fdom (fmap_lub S)"
    hence c2: "chain (\<lambda> i. the (Rep_fmap (S i) x))" (is "chain ?S2") using `chain S`
      unfolding chain_def below_fmap_def lookup.rep_eq
      by auto

    have "x \<in> fdom (S 0) " using `x \<in> fdom (fmap_lub S)` by simp
    hence "lookup (fmap_lub S) x = Some (lub (range ?S2))"
      by (auto simp add: fmap_lub.rep_eq lookup.rep_eq fmap_lub_raw_def fdom.rep_eq)        

    hence lub_at_x: "range ?S2 <<| (fmap_lub S f! x)"
      by (metis c2 the.simps thelubE)
    
    assume "x \<in> fdom u"
    have "range ?S2 <| (u f! x)"
      using ub_rangeD[OF `range S <| u`] `x \<in> fdom u`
      by (auto intro: ub_rangeI simp add:  below_fmap_def lookup.rep_eq)
     
    thus "(fmap_lub S) f! x \<sqsubseteq> u f! x"
      by (rule is_lubD2[OF lub_at_x])
  qed simp
}
qed

instance fmap :: (type, cpo) cpo
apply default
proof
  fix S :: "nat \<Rightarrow> 'a f\<rightharpoonup> 'b"
  assume "chain S"
  thus "range S <<| fmap_lub S"
    by (rule is_lub_fmap)
qed

lemma unfold_lub_fmap:  "chain (Y::nat => 'a f\<rightharpoonup> 'b::cpo) \<Longrightarrow> lub (range Y) = fmap_lub Y"
  by (rule lub_eqI, rule is_lub_fmap)

subsubsection {* Continuity and finite maps *}

lemma chain_fdom:
  assumes "chain (Y :: nat \<Rightarrow> 'a\<Colon>type f\<rightharpoonup> 'b\<Colon>cpo) "
  shows "fdom (Y i) = fdom (Y 0)" and "fdom (\<Squnion> i. Y i) = fdom (Y 0)"
proof-
    have "Y 0 \<sqsubseteq> Y i" apply (rule chain_mono[OF `chain Y`]) by simp
    thus "fdom (Y i) = fdom (Y 0)" by-(drule fmap_below_dom, rule sym)
    moreover
    have "Y 0 \<sqsubseteq> (\<Squnion>i . Y i)"  by (rule is_ub_thelub[OF `chain Y`])
    thus "fdom (\<Squnion> i. Y i) = fdom (Y 0)" by-(drule fmap_below_dom, rule sym)
qed

lemma lookup_chain:
  assumes "chain (Y :: nat \<Rightarrow> 'a f\<rightharpoonup> 'b::cpo)"
  shows "chain (\<lambda> i . (Y i) f! x)"
proof(rule chainI)
  fix i 
  have "fdom (Y i) = fdom (Y 0)" and
       "fdom (Y (Suc i)) = fdom (Y 0)" and
       "fdom (Y j) = fdom (Y 0)"
       by (intro chain_fdom[OF `chain Y`])+
  have "Y i \<sqsubseteq> Y (Suc i)" using `chain _` by (rule chainE)
    hence "fdom (Y (Suc i)) = fdom (Y i)" unfolding below_fmap_def by simp
  show "(Y i) f! x \<sqsubseteq> Y (Suc i) f! x"
    proof(cases "x \<in> fdom (Y i)")
    case True thus ?thesis using `_ \<sqsubseteq> _`  by (simp add: below_fmap_def)
    next
    case False
      hence "(Y i) f! x = the None"
        by (transfer, auto simp add: dom_def)
      moreover
      have "x \<notin> fdom (Y (Suc i))"
        using False `fdom (Y (Suc i)) = fdom (Y i)` by simp
      hence "Y (Suc i) f! x = the None"
        by (transfer, auto simp add: dom_def)
      ultimately show ?thesis by simp
    qed
qed


lemma lookup_cont:
  assumes "chain (Y :: nat \<Rightarrow> 'a f\<rightharpoonup> 'b::cpo)"
  shows "(\<Squnion> i. Y i) f! x = (\<Squnion> i. (Y i) f! x)"
proof(cases "x \<in> fdom (Y 0)")
case True thus ?thesis
  unfolding unfold_lub_fmap[OF `chain Y`]
  apply transfer
  apply (auto simp add: fmap_lub_raw_def)
  done
next
case False
  have "\<And> i. lookup (Y i) x = None"
    by (metis False assms chain_fdom(1) domIff fdom.rep_eq lookup.rep_eq)
  thus ?thesis
    unfolding unfold_lub_fmap[OF `chain Y`]
    by (transfer, auto simp add: fmap_lub_raw_def)
qed

lemma cont2cont_lookup[simp,cont2cont]:
  fixes f :: "'a::cpo \<Rightarrow> 'b::type f\<rightharpoonup> 'c::cpo"
  assumes "cont f"
  shows "cont (\<lambda>p. (f p) f! x)"
proof (rule cont_compose[OF _ `cont f`], rule contI)
  fix Y :: "nat \<Rightarrow> 'b::type f\<rightharpoonup> 'c::cpo"
  assume "chain Y"
  show "range (\<lambda>i. (Y i) f! x) <<| ((\<Squnion> i. Y i) f! x)"
    by (subst lookup_cont[OF `chain Y`], rule cpo_lubI[OF lookup_chain[OF `chain Y`]])
qed

lemma fmap_contI:
  assumes "\<And> x y . x \<sqsubseteq> y \<Longrightarrow> fdom (f x) = fdom (f y)"
  and "\<And>x y z. x \<sqsubseteq> y \<Longrightarrow> z \<in> fdom (f x) \<Longrightarrow> z \<in> fdom (f y) \<Longrightarrow> (f x) f! z \<sqsubseteq> (f y) f! z" (is "PROP ?a2")
  and "\<And> Y x. chain Y \<Longrightarrow> chain (\<lambda>i. f (Y i)) \<Longrightarrow>
       x \<in> fdom (f (\<Squnion> i. Y i)) \<Longrightarrow> x \<in> fdom (\<Squnion> i. f (Y i)) \<Longrightarrow>
       f (\<Squnion> i. Y i) f! x \<sqsubseteq> (\<Squnion> i. f (Y i)) f! x" (is "PROP ?a3") 
  shows "cont (f :: 'c::cpo \<Rightarrow> 'a f\<rightharpoonup> 'b::cpo)"
proof(intro contI2 monofunI fmap_belowI)
  fix x y :: 'c
  assume "x \<sqsubseteq> y"
  thus "fdom (f x) = fdom (f y)" using assms(1) by auto
next
  next
  fix Y
  assume c1: "chain (Y :: nat \<Rightarrow> 'c)"
  assume c2: "chain (\<lambda>i. f (Y i))"
  have "Y 0 \<sqsubseteq> Lub Y" by (metis is_ub_thelub[OF c1])
  hence "fdom (f (Y 0)) = fdom (f (Lub Y))" using assms(1) by auto
  thus "fdom (f (\<Squnion> i. Y i)) = fdom (\<Squnion> i. f (Y i))"
    by (simp add: chain_fdom(2)[OF c2])
qed fact+

lemma fmap_upd_mono:
  "\<rho>1 \<sqsubseteq> \<rho>2 \<Longrightarrow> v1 \<sqsubseteq> v2 \<Longrightarrow> \<rho>1(x f\<mapsto> v1) \<sqsubseteq> \<rho>2(x f\<mapsto> v2)"
  apply (rule fmap_belowI)
  apply (auto dest:fmap_below_dom)[1]
  apply (case_tac "xa = x")
  apply simp
  apply (auto elim:fmap_belowE)
  done

lemma fmap_upd_cont[simp,cont2cont]:
  assumes "cont f" and "cont h"
  shows "cont (\<lambda> x. fmap_upd (f x) v (h x) :: 'a f\<rightharpoonup> 'b::cpo)"
proof (intro contI2  monofunI fmap_belowI)
  fix x1 x2 :: 'c
  assume "x1 \<sqsubseteq> x2"
  hence "f x1 \<sqsubseteq> f x2" by -(erule cont2monofunE[OF `cont f`])
  thus "fdom (f x1(v f\<mapsto> h x1)) = fdom (f x2(v f\<mapsto> h x2))"
    by (simp add: fmap_below_dom)

  fix v'
  assume "v' \<in> fdom (f x1(v f\<mapsto> h x1))"  and "v' \<in> fdom (f x2(v f\<mapsto> h x2))"
  thus "f x1(v f\<mapsto> h x1) f! v' \<sqsubseteq> f x2(v f\<mapsto> h x2) f! v'"
  proof(cases "v = v'")
    case True
    thus ?thesis
      using cont2monofunE[OF `cont h` `x1 \<sqsubseteq> x2`]
      by (transfer, auto)
  next
    case False
    moreover
    with ` v' \<in> fdom (f x1(v f\<mapsto> h x1))` `v' \<in> fdom (f x2(v f\<mapsto> h x2))`
    have "v' \<in> fdom (f x1)" and "v' \<in> fdom (f x2)" by auto
    moreover
    have "f x1 f! v' \<sqsubseteq> f x2 f! v'"
      by (rule fmap_belowE[OF cont2monofunE[OF `cont f` `x1 \<sqsubseteq> x2`]])
    ultimately
    show  ?thesis  by (transfer, simp)
  qed

next
  fix Y
  assume c1: "chain (Y :: nat \<Rightarrow> 'c)"
  assume c2: "chain (\<lambda>i. f (Y i)(v f\<mapsto> h (Y i)))"
  have "Y 0 \<sqsubseteq> Lub Y" by (metis is_ub_thelub[OF c1])
  hence "f (Y 0) \<sqsubseteq> f (Lub Y)" by (rule cont2monofunE[OF `cont f`])
  hence "fdom (f (Y 0)) = fdom (f (Lub Y))" by (rule fmap_below_dom)

  thus "fdom (f (\<Squnion> i. Y i)(v f\<mapsto> h (\<Squnion> i. Y i))) = fdom (\<Squnion> i. f (Y i)(v f\<mapsto> h (Y i)))"
    by (simp add: chain_fdom(2)[OF c2])

  fix v'
  show "f (\<Squnion> i. Y i)(v f\<mapsto> h (\<Squnion> i. Y i)) f! v' \<sqsubseteq> (\<Squnion> i. f (Y i)(v f\<mapsto> h (Y i))) f! v'"
  proof(cases "v = v'")
    case True
    thus ?thesis
      using lookup_cont[OF c2]  cont2contlubE[OF `cont h` c1]
      by simp
  next
    case False
    thus ?thesis
      using lookup_cont[OF c2] cont2contlubE[OF `cont f` c1]
            lookup_cont[OF ch2ch_cont[OF `cont f` `chain Y`]]
      by simp
  qed
qed      

lemma fdom_adm[intro]: "adm (\<lambda> a. P (fdom a))" 
  by (rule admI, metis chain_fdom(2))

lemma fdom_adm_eq[simp]:
   "adm (\<lambda>\<rho>. fdom \<rho> = z)"
   by (rule fdom_adm)

lemma  fmap_add_belowI:
  assumes "fdom x \<union> fdom y = fdom z"
  and "\<And> a. a \<in> fdom y \<Longrightarrow> y f! a \<sqsubseteq> z f! a"
  and "\<And> a. a \<in> fdom x \<Longrightarrow> a \<notin> fdom y \<Longrightarrow> x f! a \<sqsubseteq> z f! a"
  shows  "x f++ y \<sqsubseteq> z"
  using assms 
  apply -
  apply (rule fmap_belowI)
  apply auto[1]
  by (metis fdomIff lookup_fmap_add1 lookup_fmap_add2)

lemma fmap_add_cont1: "cont (\<lambda> x. x f++ m::('a::type f\<rightharpoonup> 'b::cpo))"
proof(rule fmap_contI)
  fix x y :: "'a f\<rightharpoonup> 'b"
  assume "x \<sqsubseteq> y"
  hence "fdom x = fdom y" by (rule fmap_below_dom)
  thus "fdom (x f++ m) = fdom (y f++ m)"  by simp 
next
  fix x y :: "'a f\<rightharpoonup> 'b"
  assume "x \<sqsubseteq> y"
  fix z :: 'a  
  show "(x f++ m) f! z \<sqsubseteq> (y f++ m) f! z"
    using `x \<sqsubseteq> y`
    by(cases "z \<in> fdom m", auto elim: fmap_belowE)
next
  fix Y :: "nat \<Rightarrow> 'a f\<rightharpoonup> 'b"
  assume c1: "chain Y" and c2: "chain (\<lambda>i. Y i f++ m)"
  fix x :: 'a
  show "(\<Squnion> i. Y i) f++ m f! x \<sqsubseteq> (\<Squnion> i. Y i f++ m) f! x"
    by (cases "x \<in> fdom m", auto simp add: lookup_cont[OF c2] lookup_cont[OF c1])
qed

lemma fmap_add_cont2: "cont (\<lambda> x. m f++ x::('a::type f\<rightharpoonup> 'b::cpo))"
proof(rule fmap_contI)
  fix x y :: "'a f\<rightharpoonup> 'b"
  assume "x \<sqsubseteq> y"
  hence "fdom x = fdom y" by (rule fmap_below_dom)
  thus "fdom (m f++ x) = fdom (m f++ y)" by simp
next
  fix x y :: "'a f\<rightharpoonup> 'b"
  assume "x \<sqsubseteq> y"
  hence "fdom x = fdom y" by (rule fmap_below_dom)
  fix z :: 'a  
  show "m f++ x f! z \<sqsubseteq> m f++ y f! z"
    using `x \<sqsubseteq> y` `fdom x = fdom y`
    by(cases "z \<in> fdom x", auto elim: fmap_belowE)
next
  fix Y :: "nat \<Rightarrow> 'a f\<rightharpoonup> 'b"
  assume c1: "chain Y" and c2: "chain (\<lambda>i. m f++ Y i)"
    hence [simp]:"\<And> i. fdom (Y i) =  fdom (\<Squnion> i . Y i)"
      by (metis chain_fdom(1) chain_fdom(2))
  fix x :: 'a
  show "m f++ (\<Squnion> i. Y i) f! x \<sqsubseteq> (\<Squnion> i. m f++ Y i) f! x"
    by (cases "x \<in> fdom (\<Squnion> i . Y i)", auto simp add: lookup_cont[OF c2] lookup_cont[OF c1])
qed

lemma fmap_add_cont2cont[simp, cont2cont]:
  assumes "cont f"
  assumes "cont g"
  shows "cont (\<lambda> x. f x f++ (g x :: 'a f\<rightharpoonup> 'b::cpo))"
by (rule cont_apply[OF assms(1) fmap_add_cont1 cont_compose[OF fmap_add_cont2 assms(2)]])

lemma fmap_add_mono:
  assumes "x1 \<sqsubseteq> (x2 :: ('a::type f\<rightharpoonup> 'b::cpo))"
  assumes "y1 \<sqsubseteq> y2"
  shows "x1 f++ y1 \<sqsubseteq> x2 f++ y2"
by (rule below_trans[OF cont2monofunE[OF fmap_add_cont1 assms(1)] cont2monofunE[OF fmap_add_cont2 assms(2)]])

lemma fmap_upd_belowI:
  assumes "fdom \<rho>' = insert x (fdom \<rho>)"
  assumes "\<And> z . z \<in> fdom \<rho> \<Longrightarrow> z \<noteq> x \<Longrightarrow> \<rho> f! z \<sqsubseteq> \<rho>' f! z" 
  assumes "y \<sqsubseteq> \<rho>' f! x"
  shows  "\<rho>(x f\<mapsto> y) \<sqsubseteq> \<rho>'"
  apply (rule fmap_belowI)
  using assms apply simp
  using assms
  apply (case_tac "xa = x")
  apply auto
  done

lemma fmap_upd_belowI2:
  assumes "fdom \<rho> = insert x (fdom \<rho>')"
  assumes "\<And> z . z \<in> fdom \<rho> \<Longrightarrow> z \<noteq> x \<Longrightarrow> \<rho> f! z \<sqsubseteq> \<rho>' f! z" 
  assumes "\<rho> f! x \<sqsubseteq> y"
  shows  "\<rho> \<sqsubseteq> \<rho>'(x f\<mapsto> y)"
  apply (rule fmap_belowI)
  using assms apply simp
  using assms
  apply (case_tac "xa = x")
  apply auto
  done

lemma fmap_restr_belowI:
  assumes  "\<And> x. x \<in> S \<Longrightarrow> (fmap_restr S m1) f! x \<sqsubseteq> (fmap_restr S m2) f! x"
  and "fdom m1 = fdom m2"
  shows "fmap_restr S m1 \<sqsubseteq> fmap_restr S m2"
proof (cases "finite S")
case True thus ?thesis
  apply -
  apply (rule fmap_belowI)
  apply (simp add: `fdom m1 = fdom m2`)
  by (metis Int_iff assms(1) fdom_fmap_restr)
next
case False thus ?thesis unfolding fmap_restr_def by simp
qed

lemma fmap_restr_monofun:  "monofun (fmap_restr S)"
proof (cases "finite S")
  case True thus ?thesis
    apply -
    apply (rule monofunI)
    apply (rule fmap_restr_belowI)
    apply (subst lookup_fmap_restr[OF True], assumption)+
    apply (metis fmap_belowE)
    by (metis fmap_below_dom)
next
case False thus ?thesis  by -(rule monofunI, simp add: fmap_restr_def)
qed

lemma fmap_restr_cont:  "cont (fmap_restr S)"
proof(cases "finite S")
case True thus ?thesis apply -
  apply (rule contI2[OF fmap_restr_monofun])
  apply (rule fmap_belowI)
  apply (simp add: chain_fdom(2))[1]
  apply auto
  apply (subst lookup_cont, assumption)+
  apply (rule lub_mono[OF lookup_chain lookup_chain], assumption+)
  apply (subst lookup_fmap_restr[OF True], assumption)
  apply (rule below_refl)
  done
next
case False thus ?thesis by -(rule contI2[OF fmap_restr_monofun], simp add: fmap_restr_def)
qed

lemma fmap_restr_fdom_cont'[simp, cont2cont]:
  assumes "cont f"
  assumes "cont g"
  shows "cont (\<lambda> x. fmap_restr (S (fdom (f x))) (g x))"
proof (rule contI)
  case (goal1 Y)
  have [simp]:"\<And> i. fdom (f (Y i)) = fdom (f (\<Squnion>i. Y i))"
    apply (subst cont2contlubE[OF `cont f` `chain Y`])
    using ch2ch_cont[OF `cont f` `chain Y`]
    by (metis chain_fdom)
  show "?case"
    apply simp
    apply (subst cont2contlubE[OF cont_compose[OF fmap_restr_cont `cont g`] `chain Y`])
    by (metis assms(2) ch2ch_cont cpo_lubI fmap_restr_cont goal1)
qed    

lemmas fmap_restr_cont2cont[simp,cont2cont] = cont_compose[OF fmap_restr_cont]

lemma adm_less_fmap [simp]:
  "[|cont (\<lambda>x. u x); cont (\<lambda>x. v x)|] ==> adm (\<lambda>x. u x \<le> ((v x)::'a::type f\<rightharpoonup> 'b::pcpo))"
  apply (subst fmap_less_restrict)
  apply (intro adm_lemmas, assumption+)
  apply (rule contI)
  apply (subst chain_fdom(1)[OF ch2ch_cont[of u]], assumption+)
  apply (subst cont2contlubE[of u], assumption+)
  apply (subst chain_fdom(2)[OF ch2ch_cont[of u]], assumption+)
  apply (rule contE)
  apply auto
  done

subsubsection {* Expanding the domain of finite maps *}

lift_definition fmap_expand :: "'a f\<rightharpoonup> 'b::pcpo \<Rightarrow> 'a set  \<Rightarrow> 'a f\<rightharpoonup> 'b" ("_\<^bsub>[_]\<^esub>" [90, 60] 90)
  is "\<lambda> m1 S. (if finite S then (\<lambda> x. if x \<in> S then Some (case m1 x of (Some x) => x | None => \<bottom>) else None) else empty)"
  apply (case_tac "finite set")
  apply (rule_tac B = "dom fun \<union> set" in   finite_subset)
  apply auto
  done

lemma fmap_expand_nonfinite:
  "\<not> finite S \<Longrightarrow> m\<^bsub>[S]\<^esub> = f\<emptyset>"
  by (transfer, simp)

lemma fmap_restr_fmap_expand:
  "finite d2 \<Longrightarrow> fmap_restr d1 (m\<^bsub>[d2]\<^esub>) = fmap_restr d1 (m\<^bsub>[d1 \<inter> d2]\<^esub>)"
  apply(cases "finite d1")
  apply transfer
  apply (auto simp add: restrict_map_def)
  unfolding fmap_restr_def
  by auto

lemma fmap_restr_fmap_expand2:
  "finite d2 \<Longrightarrow> d1 \<subseteq> d2 \<Longrightarrow> fmap_restr d1 (m\<^bsub>[d2]\<^esub>) = m\<^bsub>[d1]\<^esub>"
  apply(cases "finite d1")
  apply transfer
  apply (auto simp add: restrict_map_def split:option.split)
  apply (metis set_mp)
  by (metis rev_finite_subset)

lemma fdom_fmap_expand[simp]:
  "finite S \<Longrightarrow> fdom (m\<^bsub>[S]\<^esub>) = S"
  by (transfer, auto split:if_splits) 

lemma fmap_expand_noop[simp]:
  "S = fdom \<rho> \<Longrightarrow> \<rho>\<^bsub>[S]\<^esub> = \<rho>"
  by (transfer, auto split: option.split)

lemma fmap_expand_idem:
  "finite S2 \<Longrightarrow> fdom \<rho> \<subseteq> S1 \<Longrightarrow> S1 \<subseteq> S2 \<Longrightarrow> (\<rho>\<^bsub>[S1]\<^esub>)\<^bsub>[S2]\<^esub> = \<rho>\<^bsub>[S2]\<^esub>"
  apply (transfer)
  apply (auto split:option.split simp add: split_if_eq1 split_if_eq2)
  apply (rule ext)
  apply (auto split:option.split simp add: split_if_eq1 split_if_eq2)
  by (metis finite_subset)

lemma lookup_fmap_expand1[simp]:
  "finite S \<Longrightarrow> x \<in> S \<Longrightarrow> x \<in> fdom m \<Longrightarrow> lookup (m\<^bsub>[S]\<^esub>) x = lookup m x"
  by (transfer, auto)

lemma lookup_fmap_expand2[simp]:
  "finite S \<Longrightarrow> x \<in> S \<Longrightarrow> x \<notin> fdom m \<Longrightarrow> lookup (m\<^bsub>[S]\<^esub>) x = Some \<bottom>"
  by (transfer, auto split:option.split)

lemma lookup_fmap_expand3[simp]:
  "finite S \<Longrightarrow> x \<notin> S \<Longrightarrow> lookup (m\<^bsub>[S]\<^esub>) x = None"
  by (transfer, auto split:option.split)

lemma fmap_expand_fdom[simp]: "\<rho>\<^bsub>[fdom \<rho>]\<^esub> = \<rho>"
  by (transfer, auto split:option.split)

lemma fmap_expand_belowI:
  assumes "fdom \<rho>' = S"
  assumes "\<And> x. x \<in> fdom \<rho> \<Longrightarrow> x \<in> S \<Longrightarrow> \<rho> f! x \<sqsubseteq> \<rho>' f! x"
  shows "\<rho>\<^bsub>[S]\<^esub> \<sqsubseteq> \<rho>'"
  apply (rule fmap_belowI)
  apply (metis assms(1) fdom_fmap_expand finite_fdom)
  apply (case_tac "x \<in> fdom \<rho>")
  apply (metis assms(1) assms(2) finite_fdom lookup_fmap_expand1)
  apply (metis assms(1) finite_fdom lookup_fmap_expand2 minimal the.simps)
  done

lemma fmap_expand_fmap_restr_below:
  assumes [simp]:"fdom x = S2"
  shows "(fmap_restr S1 x)\<^bsub>[S2]\<^esub> \<sqsubseteq> x"
  apply (rule fmap_expand_belowI[OF assms(1)])
  by (metis Int_iff below.r_refl empty_iff fdom_fmap_restr fempty_fdom fmap_restr_not_finite lookup_fmap_restr)

lemma fmap_expand_monofun:
  "monofun (\<lambda> m. m\<^bsub>[S]\<^esub>)"
proof(cases "finite S")
case True
  show ?thesis
  proof (rule monofunI, rule fmap_belowI)
  case goal1 thus *: ?case using True by (simp add: fmap_below_dom)
  case (goal2 m1 m2 x) thus ?case
    using goal2 True
    apply (cases "x \<in> S")
    apply (cases "x \<in> fdom m1")
    apply (subgoal_tac "x \<in> fdom m2")
    apply (auto dest:fmap_belowE simp add: fmap_below_dom)
    done
  qed
next
case False
  show ?thesis by (rule monofunI, simp add: fmap_expand_nonfinite[OF False])
qed

lemma fmap_expand_cont:
  "cont (\<lambda> m. m\<^bsub>[S]\<^esub>)"
proof(cases "finite S")
case True[simp]
  show ?thesis
  proof (rule fmap_contI)
  case goal1 thus ?case by (simp add: fmap_below_dom)
  case goal2 thus ?case by (metis True below_fmap_def fdom_fmap_expand lookup_fmap_expand1 lookup_fmap_expand2 minimal the.simps)
  next
  case (goal3 Y x)[simp]
    hence [simp]:"x \<in> S" by simp
    show ?case
      apply (cases "x \<in> fdom (\<Squnion> i. Y i)")
      apply (subgoal_tac "\<And> i. x \<in> fdom (Y i)")
      apply (simp add: lookup_cont)
      apply (metis chain_fdom(1) chain_fdom(2) goal3(1))
      apply (simp)
      done
  qed
next
case False
  show ?thesis by (rule contI2[OF fmap_expand_monofun] , simp add: fmap_expand_nonfinite[OF False])
qed

lemma fmap_upd_expand:
  "finite S \<Longrightarrow>
   x \<in> S \<Longrightarrow>
   \<rho>(x f\<mapsto> y)\<^bsub>[S]\<^esub> = (\<rho>\<^bsub>[S - {x}]\<^esub>)(x f\<mapsto> y)"
   apply (rule fmap_eqI, auto)
   apply (case_tac "xa \<in> fdom (\<rho>(x f\<mapsto> y))", auto)
   apply (case_tac "xa = x", auto)
   done

lemma less_fmap_expand:
  "finite S \<Longrightarrow> fdom \<rho> \<subseteq> S \<Longrightarrow> \<rho> \<le> \<rho>\<^bsub>[S]\<^esub>"
  unfolding less_eq_fmap_def
  by (transfer, auto)

subsubsection {* Bottoms *}

lemma fmap_bottom_below[simp]:
  "S = fdom \<rho> \<Longrightarrow> f\<emptyset>\<^bsub>[S]\<^esub> \<sqsubseteq> \<rho>"
 by(rule fmap_belowI, auto)

lemma fmap_bottom_below_iff[iff]:
  "finite S \<Longrightarrow> f\<emptyset>\<^bsub>[S]\<^esub> \<sqsubseteq> \<rho> \<longleftrightarrow> S = fdom \<rho>"
  by (metis fdom_fmap_expand fmap_below_dom fmap_bottom_below)

lemma fmap_bottom_inj[iff]: "finite x \<Longrightarrow> finite y \<Longrightarrow> f\<emptyset>\<^bsub>[x]\<^esub> = f\<emptyset>\<^bsub>[y]\<^esub> \<longleftrightarrow> x = y"
  by (metis below.r_refl fmap_bottom_below_iff)

lemma fmap_expand_fmap_bottom[simp]: "f\<emptyset>\<^bsub>[S']\<^esub>\<^bsub>[S]\<^esub> = f\<emptyset>\<^bsub>[S]\<^esub>"
  by (transfer, auto)

lemma fmap_restr_fmap_bottom[simp]:
  "finite S \<Longrightarrow> finite S2 \<Longrightarrow> fmap_restr S (f\<emptyset>\<^bsub>[S2]\<^esub>) = f\<emptyset>\<^bsub>[S \<inter> S2]\<^esub>"
  by auto

lemma fmap_bottom_insert:
  "finite S \<Longrightarrow>
  f\<emptyset>\<^bsub>[insert x S]\<^esub> = (f\<emptyset>\<^bsub>[S]\<^esub>)(x f\<mapsto> \<bottom>)"
  apply (rule fmap_eqI)
  apply auto[1]
  apply (case_tac "xa = x", auto)
  done

lemma fmap_bottom_less[simp]:
  "finite S2 \<Longrightarrow> S1 \<subseteq> S2 \<Longrightarrow> f\<emptyset>\<^bsub>[S1]\<^esub> \<le> f\<emptyset>\<^bsub>[S2]\<^esub>"
  apply (subgoal_tac "finite S1")
  apply (rule fmap_less_eqI)
  apply simp
  apply simp
  by (rule rev_finite_subset)

subsubsection {* A setup for defining a fixed point of finite maps iteratively *}

lemma fdom_fix_on:
  assumes "fix_on_cond S b F"
  shows  "fdom (fix_on' b F) = fdom b"
proof-
  have "fix_on' b F \<in> S"
    by (rule fix_on_there[OF assms])
  hence "b \<sqsubseteq> fix_on' b F"
    by (metis assms bottom_of_subpcpo_bot_minimal fix_on_cond.simps subpcpo_is_subpcpo_bot)
  thus ?thesis
    by (metis fmap_below_dom)
qed

locale iterative =
  fixes \<rho> :: "'a::type f\<rightharpoonup> 'b::pcpo"
   and e1 :: "'a f\<rightharpoonup> 'b \<Rightarrow> 'a f\<rightharpoonup> 'b"
   and e2 :: "'a f\<rightharpoonup> 'b \<Rightarrow> 'b"
   and S :: "'a set" and x :: 'a
   and D
  defines "D \<equiv> insert x (fdom \<rho> \<union> S)"
  assumes cont_e1 [simp]:"cont e1"
  assumes cont_e2 [simp]:"cont e2"
  assumes dom[simp]: "\<And> \<rho>. fdom (e1 \<rho>) = S"
  assumes ne:"x \<notin> S"

sublocale iterative < subpcpo "{x. f\<emptyset>\<^bsub>[D]\<^esub> \<sqsubseteq> x}" by (rule subpcpo_cone_above)

context iterative
begin

  lemma [simp]: "finite S" using dom[of undefined] by (auto simp del: dom)
  lemma [simp]: "finite D" by (simp add: D_def)
 

  abbreviation "cpo == {x. f\<emptyset>\<^bsub>[D]\<^esub> \<sqsubseteq> x}"
  abbreviation "b == f\<emptyset>\<^bsub>[D]\<^esub>"

  abbreviation "L == (\<lambda> \<rho>'. (\<rho> f++ e1 \<rho>')(x f\<mapsto> e2 \<rho>'))"
  abbreviation "H == (\<lambda> \<rho>' \<rho>''. \<rho>' f++ e1 \<rho>'')"
  abbreviation "R == (\<lambda> \<rho>'. (\<rho> f++ fmap_restr S (fix_on' b (H \<rho>')))(x f\<mapsto> e2 \<rho>'))"
  abbreviation "R' == (\<lambda> \<rho>'. (\<rho> f++ fmap_restr S (fix_on' b (H \<rho>')))(x f\<mapsto> e2 (fix_on' b (H \<rho>'))))"

  lemma condL: "fix_on_cond cpo b L"
    apply (rule fix_on_condI)
    apply (rule subpcpo_cone_above)
    apply (rule bottom_of_cone_above)
    apply (rule closed_onI)
      apply (simp add: D_def)
    apply (rule cont_is_cont_on)
      apply simp
    done
  lemmas [simp] = fdom_fix_on[OF condL]

  lemma condH: "\<And> \<rho>'. \<rho>' \<in> cpo \<Longrightarrow> fix_on_cond cpo b (H \<rho>')"
    apply (rule fix_on_condI)
    apply (rule subpcpo_cone_above)
    apply (rule bottom_of_cone_above)
    apply (rule closed_onI)
      apply (auto simp add: D_def)[1]
    apply (rule cont_is_cont_on)
      apply simp
    done
  lemmas [simp] = fdom_fix_on[OF condH]
  
  lemma condR: "fix_on_cond cpo b R"
    apply (rule fix_on_condI)
    apply (rule subpcpo_cone_above)
    apply (rule bottom_of_cone_above)
    apply (rule closed_onI)
      using fdom_fix_on[OF condH]  apply (auto simp add: D_def)[1]
    apply (rule cont_comp_cont_on2[OF cont2cont_lambda[OF fmap_upd_cont[OF cont_id cont_const]]
                fmap_upd_cont[OF cont_const cont_id]
                _
                cont_is_cont_on[OF cont_e2]])
    apply (rule cont_comp_cont_on2[OF cont2cont_lambda[OF fmap_add_cont1]
                fmap_add_cont2
                cont_is_cont_on[OF cont_const]
                ])
    apply (rule cont_comp_cont_on[OF fmap_restr_cont])
    apply (rule cont_onI2)
      apply (rule monofun_onI)
      apply (erule (1) fix_on_mono[OF condH condH])
      apply (erule cont2monofunE[OF fmap_add_cont1])

    apply (rule eq_imp_below)
    apply (rule fix_on_cont[OF chain_on_is_chain condH[OF chain_on_is_on]])
      apply assumption
      apply assumption
    apply (rule cont2cont_lambda[OF fmap_add_cont1])
    done
  lemmas [simp] = fdom_fix_on[OF condR]

  lemma cont_on_fix_H: "cont_on (\<lambda> \<rho>'. fix_on' b (H \<rho>'))"
    apply (rule cont_onI2)
      apply (rule monofun_onI)
      apply (erule (1) fix_on_mono[OF condH condH])
      apply (erule cont2monofunE[OF fmap_add_cont1])

    apply (rule eq_imp_below)
    apply (rule fix_on_cont[OF chain_on_is_chain condH[OF chain_on_is_on]])
      apply assumption
      apply assumption
    apply (rule cont2cont_lambda[OF fmap_add_cont1])
    done

  lemma condR': "fix_on_cond cpo b R'"
    apply (rule fix_on_condI)
    apply (rule subpcpo_cone_above)
    apply (rule bottom_of_cone_above)
    apply (rule closed_onI)
      using fdom_fix_on[OF condH]  apply (auto simp add: D_def)[1]
    apply (rule cont_comp_cont_on2[OF cont2cont_lambda[OF fmap_upd_cont[OF cont_id cont_const]]
                fmap_upd_cont[OF cont_const cont_id]
                _
                cont_comp_cont_on[OF cont_e2 cont_on_fix_H]])
    apply (rule cont_comp_cont_on2[OF cont2cont_lambda[OF fmap_add_cont1]
                fmap_add_cont2
                cont_is_cont_on[OF cont_const]
                ])
    apply (rule cont_comp_cont_on[OF fmap_restr_cont cont_on_fix_H])
    done
  lemmas [simp] = fdom_fix_on[OF condR']

  lemmas fix_eq_R = fix_on_eq[OF condR]
  lemmas fix_eq_R' = fix_on_eq[OF condR']
  lemmas fix_eq_L = fix_on_eq[OF condL]
  lemmas fix_eq_HL = fix_on_eq[OF condH[OF fix_on_there[OF condL]]]
  lemmas fix_eq_HR = fix_on_eq[OF condH[OF fix_on_there[OF condR]]]
  lemmas fix_eq_HR' = fix_on_eq[OF condH[OF fix_on_there[OF condR']]]

  lemma [simp]: "D \<inter> S = S" 
      by (auto simp add: D_def)

  lemma HR_not_S[simp]: "\<And> x. x \<notin> S \<Longrightarrow> lookup (fix_on' b (H (fix_on' b R))) x = lookup (fix_on' b R) x"
      apply (subst fix_eq_HR) by simp
  
  lemma HR_S[simp]: "\<And> y. y \<in> S \<Longrightarrow> lookup (fix_on' b (H (fix_on' b R))) y = lookup (e1 (fix_on' b (H (fix_on' b R)))) y"
    apply (subgoal_tac "y \<noteq> x")
    apply (subst fix_eq_HR)
    apply simp
    using ne by metis

  lemma L_S[simp]: "\<And> y. y \<in> S \<Longrightarrow> lookup (fix_on' b L) y = lookup (e1 (fix_on' b L)) y"
    apply (subgoal_tac "y \<noteq> x")
    apply (subst (1) fix_eq_L)
    apply simp
    using ne by metis

  lemma L_x2[simp]: "(fix_on' b L) f! x = e2 (fix_on' b L)"
    by (subst (1) fix_eq_L, simp)

  lemma L_not_S_x2[simp]: "\<And> y. y \<notin> S \<Longrightarrow> y \<noteq> x \<Longrightarrow> lookup (fix_on' b L) y = lookup \<rho> y"
    by (subst (1) fix_eq_L, simp)

  lemma R_S[simp]: "\<And> y. y \<in> S \<Longrightarrow> lookup (fix_on' b R) y = lookup (e1 (fix_on' b (H (fix_on' b R)))) y"
    apply (subgoal_tac "y \<noteq> x")
    apply (subst fix_eq_R)
    apply simp
    using ne by metis

  lemma R_x2[simp]: "(fix_on' b R) f! x = e2 (fix_on' b R)"
    by (subst fix_eq_R, simp)

  lemma R_not_S[simp]: "\<And> y. y \<notin> S \<Longrightarrow> y \<noteq> x \<Longrightarrow> lookup (fix_on' b R) y = lookup \<rho> y"
    by (subst fix_eq_R, simp)

  lemma HR_is_R[simp]: "fix_on' b (H (fix_on' b R)) = fix_on' b R"
    apply (rule fmap_eqI)
    apply simp
    apply (case_tac "xa \<in> S")
    apply simp_all
    done

  lemma HL_not_S[simp]: "\<And> x. x \<notin> S \<Longrightarrow> lookup (fix_on' b (H (fix_on' b L))) x = lookup (fix_on' b L) x"
    apply (subst fix_eq_HL) by simp

  lemma HR'_not_S[simp]: "\<And> x. x \<notin> S \<Longrightarrow> lookup (fix_on' b (H (fix_on' b R'))) x = lookup (fix_on' b R') x"
    apply (subst fix_eq_HR') by simp

  lemma HR'_S[simp]: "\<And> y. y \<in> S \<Longrightarrow> lookup (fix_on' b (H (fix_on' b R'))) y = lookup (e1 (fix_on' b (H (fix_on' b R')))) y"
    apply (subgoal_tac "y \<noteq> x")
    apply (subst fix_eq_HR')
    apply simp
    using ne by metis

  lemma HL_S[simp]: "\<And> y. y \<in> S \<Longrightarrow> lookup (fix_on' b (H (fix_on' b L))) y = lookup (e1 (fix_on' b (H (fix_on' b L)))) y"
    apply (subgoal_tac "y \<noteq> x")
    apply (subst fix_eq_HL)
    apply simp
    using ne by metis

  lemma R'_S[simp]: "\<And> y. y \<in> S \<Longrightarrow> lookup (fix_on' b R') y = lookup (e1 (fix_on' b (H (fix_on' b R')))) y"
    apply (subgoal_tac "y \<noteq> x")
    apply (subst fix_eq_R')
    apply simp
    using ne by metis

  lemma R'_x2[simp]: "(fix_on' b R') f! x = e2 (fix_on' b (H (fix_on' b R')))"
    by (subst fix_eq_R', simp)

  lemma R'_not_S[simp]: "\<And> y. y \<notin> S \<Longrightarrow> y \<noteq> x \<Longrightarrow> lookup (fix_on' b R') y = lookup \<rho> y"
    by (subst fix_eq_R', simp)

  lemma HR'_is_R'[simp]: "fix_on' b (H (fix_on' b R')) = fix_on' b R'"
    apply (rule fmap_eqI)
    apply simp
    apply (case_tac "xa \<in> S")
    apply simp_all
    done
  
  lemma H_noop:
    fixes \<rho>' \<rho>''
    assumes there: "(\<rho>' :: 'a f\<rightharpoonup> 'b) \<in> cpo"
    assumes "\<And> x. x \<in> S \<Longrightarrow> (e1 \<rho>'') f! x \<sqsubseteq> \<rho>' f! x"
    shows "H \<rho>' \<rho>'' \<sqsubseteq> \<rho>'"
      using assms
      apply -
      apply (rule fmap_belowI)
      using there apply (auto simp add: D_def)[1]
      apply (case_tac "x \<in> fdom (e1 \<rho>')")
      apply simp
      apply simp
      done

  lemma HL_is_L[simp]: "fix_on' b (H (fix_on' b L)) = fix_on' b L"
  proof (rule below_antisym)
    show "fix_on' b (H (fix_on' b L)) \<sqsubseteq> fix_on' b L"
      apply (rule fix_on_least_below[OF condH[OF fix_on_there[OF condL]] fix_on_there[OF condL]])
      apply (rule H_noop[OF fix_on_there[OF condL]])
      apply simp
    done

    show "fix_on' b L \<sqsubseteq> fix_on' b (H (fix_on' b L))"
    apply (rule fix_on_least_below[OF condL fix_on_there[OF condH[OF fix_on_there[OF condL]]]])
    apply (rule fmap_upd_belowI)
    apply simp apply (auto simp add: D_def)[1]
    apply (case_tac "z \<in> S")
    apply simp
    apply simp
    apply (simp add: ne)
    apply (rule cont2monofunE[OF cont_e2])
    apply fact
    done
  qed


  lemma HLL_below_L: "H (fix_on' b L) (fix_on' b L) \<sqsubseteq> (fix_on' b L)"
    by (rule H_noop, simp_all)

  
  lemma iterative_fmap_add:
    shows "fix_on' b L = fix_on' b R"
  proof(rule below_antisym)
    show "fix_on' b R \<sqsubseteq> fix_on' b L"
    proof (rule fix_on_least_below[OF condR])
      show "fix_on' b L \<in> cpo"
        by simp
      show "R (fix_on' b L) \<sqsubseteq> fix_on' b L"
      proof(rule fmap_upd_belowI)
        case goal1 show ?case by (simp, auto simp add: D_def)
        show "e2 (fix_on' b L) \<sqsubseteq> (fix_on' b L) f! x"
          by simp
        case (goal2 y)
          hence [simp]:"y \<noteq> x" by metis
        show "\<rho> f++ fmap_restr S (fix_on' b (H (fix_on' b L))) f! y \<sqsubseteq> (fix_on' b L) f! y"
        proof(cases "y \<in> S")
        case True[simp]
          from HLL_below_L
          have "(fix_on' b (H (fix_on' b L))) \<sqsubseteq> (fix_on' b L)"
            by (rule fix_on_least_below[OF condH[OF fix_on_there[OF condL]] fix_on_there[OF condL]])
          hence "fix_on' b (H (fix_on' b L)) f! y \<sqsubseteq> fix_on' b L f! y"
            by (rule fmap_belowE)
          thus ?thesis
            by (subst lookup_fmap_add1, simp_all)
        next
        case False
          thus ?thesis by simp
        qed
      qed
    qed
  
    show "fix_on' b L \<sqsubseteq> fix_on' b R"
    proof (rule fix_on_least_below[OF condL])
      show "fix_on' b R \<in> cpo"
        by simp
      show "L (fix_on' b R) \<sqsubseteq> fix_on' b R"
        apply (rule  fmap_upd_belowI)
        apply simp apply (auto simp add: D_def)[1]
        apply (case_tac "z \<notin> S")
        apply simp_all
      done
    qed
  qed

  lemma iterative_fmap_add':
    shows "fix_on' b L = fix_on' b R'"
  proof(rule below_antisym)
    show "fix_on' b R' \<sqsubseteq> fix_on' b L"
    proof (rule fix_on_least_below[OF condR'])
      show "fix_on' b L \<in> cpo"
        by simp
      show "R' (fix_on' b L) \<sqsubseteq> fix_on' b L"
      proof(rule fmap_upd_belowI)
        case goal1 show ?case by (simp, auto simp add: D_def)
        show "e2 (fix_on' b (H (fix_on' b L))) \<sqsubseteq> (fix_on' b L) f! x"
          by simp
        case (goal2 y)
          hence [simp]:"y \<noteq> x" by metis
        show "\<rho> f++ fmap_restr S (fix_on' b (H (fix_on' b L))) f! y \<sqsubseteq> fix_on' b L f! y"
        proof(cases "y \<in> S")
        case True[simp]
          from HLL_below_L
          have "(fix_on' b (H (fix_on' b L))) \<sqsubseteq> (fix_on' b L)"
            by (rule fix_on_least_below[OF condH[OF fix_on_there[OF condL]] fix_on_there[OF condL]])
          hence "fix_on' b (H (fix_on' b L)) f! y \<sqsubseteq> fix_on' b L f! y"
            by (rule fmap_belowE)
          thus ?thesis
            by (subst lookup_fmap_add1, simp_all)
        next
        case False
          thus ?thesis by simp
        qed
      qed
    qed
  
    show "fix_on' b L \<sqsubseteq> fix_on' b R'"
    proof (rule fix_on_least_below[OF condL])
      show "fix_on' b R' \<in> cpo"
        by simp
      show "L (fix_on' b R') \<sqsubseteq> fix_on' b R'"
        apply (rule  fmap_upd_belowI)
        apply simp apply (auto simp add: D_def)[1]
        apply (case_tac "z \<notin> S")
        apply simp_all
      done
    qed
  qed
end

subsubsection {* Finite maps have greatest lowest bounds *}

instance fmap :: (type, Nonempty_Meet_cpo) Bounded_Nonempty_Meet_cpo
apply default
proof-
  fix S :: "('a f\<rightharpoonup> 'b) set"
  assume "S \<noteq> {}" and "\<exists>z. S >| z"
  then obtain b where "\<And> m. m\<in>S \<Longrightarrow> b \<sqsubseteq> m" by (metis is_lbD)
  hence [simp]:"\<And> m. m \<in> S \<Longrightarrow> fdom m = fdom b" by (metis fmap_below_dom)
  
  obtain f where f: "\<And> x. x \<in> fdom b \<Longrightarrow> (\<lambda>m . m f! x) ` S >>| f x "
  proof-
    {
    fix x
    assume "x \<in> fdom b"
    have "(\<lambda>m . m f! x) ` S \<noteq> {}" using `S \<noteq> {}` by auto
    then obtain l where  "(\<lambda>m . m f! x) ` S >>| l" by (metis nonempty_meet_exists)
    hence "(\<lambda>m . m f! x) ` S >>| (SOME l. (\<lambda>m . m f! x) ` S >>| l)"
      by (rule someI)
    }
    thus ?thesis by (rule that)
  qed 

  let ?zm = "\<lambda> x. if x \<in> fdom b then Some (f x) else None"
  have "dom ?zm = fdom b" by (auto simp add: dom_def)

  obtain z where [simp]: "fdom z = fdom b" and z: "\<And> x m . x \<in> fdom b \<Longrightarrow> (\<lambda>m . m f! x) ` S >>| (z f! x)"
  proof-
    show ?thesis  
      apply (rule that[of "Abs_fmap ?zm"])
      apply (subst fdom.rep_eq)
      apply (subst  Abs_fmap_inverse)
      prefer 3
      apply (subst (2) lookup.rep_eq)
      apply (subst  Abs_fmap_inverse)
      apply (auto simp add: dom_def)
      apply (erule f)
      done
  qed

  have "S >>| z"
    apply (rule is_glbI)
    apply (rule is_lbI)
    apply (rule fmap_belowI)
    apply simp
    apply (rule is_lbD)
    apply (rule is_glbD1)
    apply (rule z, simp)
    apply auto
    apply (rule fmap_belowI)
    apply (metis `S \<noteq> {}` `\<And>m. m \<in> S \<Longrightarrow> fdom m = fdom b` `fdom z = fdom b` all_not_in_conv fmap_below_dom is_lbD)
    apply (rule is_glbD2)
    apply (rule z, simp)
    apply (rule is_lbI)
    apply (erule imageE)
    apply (erule ssubst)
    apply (rule fmap_belowE)
    apply (erule (1) is_lbD)
    done
  thus "\<exists> z. S >>| z" by auto
qed

subsubsection {* Finite maps can be partitioned in pcpo's *} 

instantiation fmap :: (type, pcpo) subpcpo_partition
begin
  definition "to_bot x = f\<emptyset>\<^bsub>[fdom x]\<^esub>"
  lemma [simp]:"fdom (to_bot x) = fdom x"
    unfolding to_bot_fmap_def by auto

  lemma to_bot_vimage_cone:"to_bot -` {to_bot x} = {z. f\<emptyset>\<^bsub>[fdom x]\<^esub> \<sqsubseteq> z}"
    by (auto simp add:to_bot_fmap_def)

  instance  
  apply default
  apply (subst to_bot_vimage_cone)
  apply (rule subpcpo_cone_above)
  apply (simp add: to_bot_fmap_def fmap_below_dom)
  apply (simp add: to_bot_fmap_def)
  done
end

subsubsection {* Binary joins of finite maps *}

lemma fdom_join[simp]:
  "compatible m1 m2 \<Longrightarrow> fdom (m1 \<squnion> m2) = fdom m1"
  by (metis join_above1 fmap_below_dom)

lemma fdom_compatible:
  "compatible m1 m2 \<Longrightarrow> fdom m1 = fdom m2"
by (metis join_above1 join_above2 fmap_below_dom)

lemma the_lookup_compatible_and_join: 
  assumes "compatible m1 m2"
  assumes [simp]: "x \<in> fdom m1"
  shows "compatible (m1 f! x) (m2 f! x) \<and> (m1 f! x) \<squnion> (m2 f! x) = (m1 \<squnion> m2) f! x"
proof (rule is_join_and_compatible)
  show "m1 f! x \<sqsubseteq> (m1 \<squnion> m2) f! x"
    by (rule fmap_belowE[OF join_above1[OF `compatible m1 m2`]])
  show "m2 f! x \<sqsubseteq> (m1 \<squnion> m2) f! x"
    by (rule fmap_belowE[OF join_above2[OF `compatible m1 m2`]])
  fix a
  assume "m1 f! x \<sqsubseteq> a"
  assume "m2 f! x \<sqsubseteq> a"

  note fdom_compatible[OF `compatible m1 m2`, symmetric, simp]
  note fdom_join[OF `compatible m1 m2`, simp]

  have "m1 \<sqsubseteq> (m1 \<squnion> m2)(x f\<mapsto> a)"
    apply (rule fmap_upd_belowI2)
    apply auto[1]
    apply (rule fmap_belowE[OF join_above1[OF `compatible m1 m2`]])
    apply (rule `m1 f! x \<sqsubseteq> a`)
    done
  moreover
  have "m2 \<sqsubseteq> (m1 \<squnion> m2)(x f\<mapsto> a)"
    apply (rule fmap_upd_belowI2)
    apply auto[1]
    apply (rule fmap_belowE[OF join_above2[OF `compatible m1 m2`]])
    apply (rule `m2 f! x \<sqsubseteq> a`)
    done
  ultimately
  have "(m1 \<squnion> m2) \<sqsubseteq> (m1 \<squnion> m2)(x f\<mapsto> a)"
    by (rule join_below[OF `compatible m1 m2`])
  thus " m1 \<squnion> m2 f! x \<sqsubseteq> a"
    by (metis (full_types) fmap_belowE the.simps the_lookup_fmap_upd)
qed

lemma the_lookup_join[simp]: 
  assumes "compatible m1 m2"
  shows "(m1 \<squnion> m2) f! x = (m1 f! x) \<squnion> (m2 f! x)"
  apply (cases "x \<in> fdom m1")
  apply (metis assms the_lookup_compatible_and_join)
  apply (metis assms fdomIff fdom_compatible fdom_join join_self)
  done

lemma the_lookup_compatible:
  assumes "compatible m1 m2"
  shows "compatible (m1 f! x) (m2 f! x)" 
  apply (cases "x \<in> fdom m1")
  apply (metis assms the_lookup_compatible_and_join)
  apply (metis assms compatible_refl fdomIff fdom_compatible)
  done

lift_definition fmap_join :: "'a f\<rightharpoonup> 'b::cpo \<Rightarrow> 'a f\<rightharpoonup> 'b  \<Rightarrow> 'a f\<rightharpoonup> 'b"
is "\<lambda>m1 m2 x. (if x \<in> fdom m1 then Some ((m1 f! x) \<squnion> (m2 f! x)) else None)"
  by (auto simp add: dom_def)

lemma fdom_fmap_join'[simp]: "fdom (fmap_join m1 m2) = fdom m1"
  apply (subst fdom.rep_eq)
  apply (subst fmap_join.rep_eq)
  apply (auto, metis not_Some_eq)
  done

lemma the_lookup_fmap_join'[simp]: "x \<in> fdom m1 \<Longrightarrow> (fmap_join m1 m2) f! x = (m1 f! x) \<squnion> (m2 f! x)"
  apply (subst lookup.rep_eq)
  apply (subst fmap_join.rep_eq)
  apply simp
  done

lemma compatible_fmapI:
  assumes "\<And> x. \<lbrakk> x \<in> fdom m1 ; x \<in> fdom m2 \<rbrakk> \<Longrightarrow> compatible (m1 f! x) (m2 f! x)"
  assumes "fdom m1 = fdom m2"
  shows "compatible m1 m2"
proof (rule compatibleI)
  show "m1 \<sqsubseteq> fmap_join m1 m2"
    apply (rule fmap_belowI)
    apply simp
    apply simp
    by (metis "HOLCF-Join.join_above1" assms(1) assms(2))
  show "m2 \<sqsubseteq> fmap_join m1 m2"
    apply (rule fmap_belowI)
    apply (simp add: assms(2))
    apply (simp add: assms(2))
    by (metis "HOLCF-Join.join_above2" assms(1) assms(2))
  fix a
  assume "m1 \<sqsubseteq> a"
  assume "m2 \<sqsubseteq> a"
  show "fmap_join m1 m2 \<sqsubseteq> a"
    apply (rule fmap_belowI)
    apply (metis fdom_fmap_join' fmap_below_dom[OF `m1 \<sqsubseteq> a`])
    apply (metis fmap_belowE[OF `m1 \<sqsubseteq> a`] fmap_belowE[OF `m2 \<sqsubseteq> a`] assms(1) assms(2) fdom_fmap_join' join_below the_lookup_fmap_join')
    done
qed

lemma fmap_restr_join:
  assumes [simp]: "finite S"
  assumes [simp]:"compatible m1 m2"
  shows "fmap_restr S (m1 \<squnion> m2) = fmap_restr S m1 \<squnion> fmap_restr S m2"
proof-
  have [simp]: "compatible (fmap_restr S m1) (fmap_restr S m2)"
    by (auto intro!: compatible_fmapI simp add: the_lookup_compatible fdom_compatible[OF assms(2)])
  show ?thesis
    by (rule fmap_eqI, auto)
qed

lemma fmap_upd_join:
  assumes "S = insert x (fdom \<rho>1)"
  and "x \<notin> fdom \<rho>1"
  and "x \<notin> fdom \<rho>2"
  and compat1: "compatible (\<rho>1(x f\<mapsto> y)) (\<rho>2\<^bsub>[S]\<^esub>)"
  shows "(\<rho>1(x f\<mapsto> y)) \<squnion> (\<rho>2\<^bsub>[S]\<^esub>) = (\<rho>1 \<squnion> (\<rho>2\<^bsub>[S - {x}]\<^esub>))(x f\<mapsto> y)" (is "?L = ?R")
proof(rule fmap_eqI)
  have "finite S" using assms(1) by auto

  have *: "\<And> xa . xa \<in> S \<Longrightarrow> xa \<noteq> x \<Longrightarrow> \<rho>2\<^bsub>[S - {x}]\<^esub> f! xa = \<rho>2\<^bsub>[S]\<^esub> f! xa"
    using `finite S` by (case_tac "xa \<in> fdom \<rho>2", auto)

  have compat2: "compatible \<rho>1 (\<rho>2\<^bsub>[S - {x}]\<^esub>)"
    apply (rule compatible_fmapI)
    using compat1
    apply -
    apply (drule_tac x = xa in the_lookup_compatible)
    apply (subst *)
    using assms(1) apply simp
    apply (metis assms(2))

    apply (subst (asm) the_lookup_fmap_upd_other)
    apply (metis `x \<notin> fdom \<rho>1`)
    apply assumption
    using assms(2) assms(1)
    by auto

  show "fdom ?L = fdom ?R"
    using compat1 compat2 by auto
  fix y
  assume "y \<in> fdom ?L"
  hence "y \<in> S" by (metis assms(1) compat1 fdom_join fmap_upd_fdom)
  show "?L f! y = ?R f! y"
  proof(cases "y = x")
    case True
    thus ?thesis
      apply (subst the_lookup_join[OF compat1])
      apply (subst lookup_fmap_expand2[OF `finite S` `y\<in> S`])
      using `x \<notin> fdom \<rho>2` compat2  `y\<in> S`
      by auto
  next
    case False
    thus ?thesis
      apply simp
      apply (subst the_lookup_join[OF compat1], auto)
      apply (subst the_lookup_join[OF compat2])
      apply (case_tac "y \<in> fdom \<rho>2")
      using `finite S`  `y \<in> S`
      by auto
  qed
qed

end
