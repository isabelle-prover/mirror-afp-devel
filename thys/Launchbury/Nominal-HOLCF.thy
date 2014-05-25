theory "Nominal-HOLCF"
imports
  "Nominal2" "Nominal-Utils" "HOLCF-Utils"
begin

subsubsection {* Type class of continous permutations and variations thereof *}

class cont_pt = 
  cpo + 
  pt +
  assumes perm_cont: "\<And>p. cont ((permute p) :: 'a::{cpo,pt} \<Rightarrow> 'a)"

class discr_pt = 
  discrete_cpo + 
  pt

class pcpo_pt = 
  cont_pt + 
  pcpo

instance pcpo_pt \<subseteq> cont_pt
 by (default, auto intro: perm_cont)

instance discr_pt \<subseteq> cont_pt
 by (default, auto)

lemma (in cont_pt) perm_cont_simp[simp]: "\<pi> \<bullet> x \<sqsubseteq> \<pi> \<bullet> y \<longleftrightarrow> x \<sqsubseteq> y"
  apply rule
  apply (drule cont2monofunE[OF perm_cont, of _ _ "-\<pi>"], simp)[1]
  apply (erule cont2monofunE[OF perm_cont, of _ _ "\<pi>"])
  done

lemma perm_is_ub_simp[simp]: "\<pi> \<bullet> S <| \<pi> \<bullet> (x::'a::cont_pt) \<longleftrightarrow> S <| x"
  by (auto simp add: is_ub_def permute_set_def)

lemma perm_is_ub_eqvt[simp,eqvt]: "S <| (x::'a::cont_pt) \<Longrightarrow> \<pi> \<bullet> S <| \<pi> \<bullet> x"
  by simp

lemma perm_is_lub_simp[simp]: "\<pi> \<bullet> S <<| \<pi> \<bullet> (x::'a::cont_pt) \<longleftrightarrow> S <<| x"
  apply (rule perm_rel_lemma)
  by (metis is_lubI is_lubD1 is_lubD2 perm_cont_simp perm_is_ub_simp)

lemma perm_is_lub_eqvt[simp,eqvt]: "S <<| (x::'a::cont_pt) ==> \<pi> \<bullet> S <<| \<pi> \<bullet> x"
  by simp

lemmas perm_cont2cont[simp,cont2cont] = cont_compose[OF perm_cont]

lemma perm_still_cont: "cont (\<pi> \<bullet> f) = cont (f :: ('a :: cont_pt) \<Rightarrow> ('b :: cont_pt))"
proof
  have imp:"\<And> (f :: 'a \<Rightarrow> 'b) \<pi>. cont f \<Longrightarrow> cont (\<pi> \<bullet> f)"
    unfolding permute_fun_def
    by (metis cont_compose perm_cont)
  show "cont f \<Longrightarrow> cont (\<pi> \<bullet> f)" using imp[of "f" "\<pi>"].
  show "cont (\<pi> \<bullet> f) \<Longrightarrow> cont (f)" using imp[of "\<pi> \<bullet> f" "-\<pi>"] by simp
qed

lemma perm_bottom[simp,eqvt]: "\<pi> \<bullet> \<bottom> = (\<bottom>::'a::{cont_pt,pcpo})"
  proof-
  have "\<bottom> \<sqsubseteq> -\<pi> \<bullet> (\<bottom>::'a::{cont_pt,pcpo})" by simp
  hence "\<pi> \<bullet> \<bottom> \<sqsubseteq> \<pi> \<bullet> (-\<pi> \<bullet> (\<bottom>::'a::{cont_pt,pcpo}))" by(rule cont2monofunE[OF perm_cont])
  hence "\<pi> \<bullet> \<bottom> \<sqsubseteq> (\<bottom>::'a::{cont_pt,pcpo})" by simp
  thus "\<pi> \<bullet> \<bottom> = (\<bottom>::'a::{cont_pt,pcpo})" by simp
qed

lemma bot_supp[simp]: "supp (\<bottom> :: 'a :: pcpo_pt) = {}"
  by (rule supp_fun_eqvt) (simp add: eqvt_def)

lemma bot_fresh[simp]: "a \<sharp> (\<bottom> :: 'a :: pcpo_pt)"
  by (simp add: fresh_def)

lemma bot_fresh_star[simp]: "a \<sharp>* (\<bottom> :: 'a :: pcpo_pt)"
  by (simp add: fresh_star_def)

lemma below_eqvt [eqvt]:
    "\<pi> \<bullet> (x \<sqsubseteq> y) = (\<pi> \<bullet> x \<sqsubseteq> \<pi> \<bullet> (y::'a::cont_pt))" by (auto simp add: permute_pure)

lemma lub_eqvt[simp]:
  "(\<exists> z. S <<| (z::'a::{cont_pt})) \<Longrightarrow> \<pi> \<bullet> lub S = lub (\<pi> \<bullet> S)"
  by (metis lub_eqI perm_is_lub_simp)

lemma chain_eqvt[eqvt]:
  fixes F :: "nat \<Rightarrow> 'a::cont_pt"
  shows "chain F \<Longrightarrow> chain (\<pi> \<bullet> F)"
  apply (rule chainI)
  apply (drule_tac i = i in chainE)
  apply (subst (asm) perm_cont_simp[symmetric, where \<pi> = \<pi>])
  by (metis permute_fun_app_eq permute_pure)

subsubsection {* Instance for @{type cfun} *}

instantiation "cfun" :: (cont_pt, cont_pt) pt
begin
  definition "p \<bullet> (f :: 'a  \<rightarrow> 'b) = (\<Lambda> x. p \<bullet> (f \<cdot> (- p \<bullet> x)))"

  instance
  apply(default)
  apply (simp add: permute_cfun_def eta_cfun)
  apply (simp add: permute_cfun_def cfun_eqI minus_add)
  done
end

lemma permute_cfun_eq: "permute p = (\<lambda> f. (Abs_cfun (permute p)) oo f oo (Abs_cfun (permute (-p))))"
  by (rule, rule cfun_eqI, auto simp add: permute_cfun_def)

lemma Cfun_app_eqvt[eqvt]:
  "\<pi> \<bullet> (f \<cdot> x) = (\<pi> \<bullet> f) \<cdot> (\<pi> \<bullet> x)"
  unfolding permute_cfun_def
  by auto

lemma permute_Lam: "cont f \<Longrightarrow> p \<bullet> (\<Lambda> x. f x) = (\<Lambda> x. (p \<bullet> f) x)"
  apply (rule cfun_eqI)
  unfolding permute_cfun_def
  by (metis Abs_cfun_inverse2 eqvt_lambda unpermute_def )

lemma Abs_cfun_eqvt: "cont f \<Longrightarrow> (p \<bullet> Abs_cfun) f = Abs_cfun f"
  apply (subst permute_fun_def)
  by (metis permute_Lam perm_still_cont permute_minus_cancel(1))

instance "cfun" :: (cont_pt, cont_pt) cont_pt
  by (default,subst permute_cfun_eq, auto)

instance "cfun" :: ("{pure,cont_pt}", "{pure,cont_pt}") pure
  by default (auto  simp add: permute_cfun_def permute_pure Cfun.cfun.Rep_cfun_inverse)

instance "cfun" :: (cont_pt, pcpo_pt) pcpo_pt
  by (default)

subsubsection {* Instance for @{type fun} *}

lemma permute_fun_eq: "permute p = (\<lambda> f. (permute p) \<circ> f \<circ> (permute (-p)))"
  by (rule, rule, metis comp_apply eqvt_lambda unpermute_def)

instance "fun" :: (pt, cont_pt) cont_pt
  apply (default)
  apply (rule cont2cont_lambda)
  apply (subst permute_fun_def)
  apply (rule perm_cont2cont)
  apply (rule cont_fun)
  done


lemma adm_subst2: "cont f \<Longrightarrow> cont g \<Longrightarrow> adm (\<lambda>x. f (fst x) = g (snd x))"
  apply (rule admI)
  apply (simp add:
      cont2contlubE[where f = f]  cont2contlubE[where f = g]
      cont2contlubE[where f = snd]  cont2contlubE[where f = fst]
      )
  done

lemma fix_eqvt[eqvt]:
  "\<pi> \<bullet> fix = (fix :: ('a \<rightarrow> 'a) \<rightarrow> 'a::{cont_pt,pcpo})"
apply (rule cfun_eqI)
apply (subst permute_cfun_def)
apply simp
apply (rule parallel_fix_ind[OF adm_subst2])
apply (auto simp add: permute_self)
done

end
