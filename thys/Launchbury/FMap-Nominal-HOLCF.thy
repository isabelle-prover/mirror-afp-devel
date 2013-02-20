theory "FMap-Nominal-HOLCF"
imports "Nominal-HOLCF" "FMap-Nominal" "FMap-HOLCF" "Nominal-Utils"
begin

subsubsection {* Permutation of finite maps is continuous *}

instance "fmap" :: (pt, cont_pt) cont_pt
apply default
proof(intro contI2 monofunI fmap_belowI)
  fix \<pi> m1 m2
  assume "m1 \<sqsubseteq> (m2 :: 'a f\<rightharpoonup> 'b)"
  hence "fdom m1 = fdom m2"
    by (rule fmap_below_dom)

  show "fdom (\<pi> \<bullet> m1) = fdom (\<pi> \<bullet> m2)"
    using `fdom m1 = fdom m2`
    by (metis fdom_perm_rev)

  fix x
  assume "x \<in> fdom (\<pi> \<bullet> m1)" and "x \<in> fdom (\<pi> \<bullet> m2)"
  moreover
  obtain x2 where "x = \<pi> \<bullet> x2" by (metis eqvt_bound)
  ultimately
  have "x2 \<in> fdom m1" "x2 \<in> fdom m2"
    using `x \<in> fdom (\<pi> \<bullet> m1)` `x \<in> fdom (\<pi> \<bullet> m2)`
    by (metis (full_types) fdom_perm_rev mem_permute_iff)+

  have "(\<pi> \<bullet> m1) f! x = \<pi> \<bullet> (m1 f! x2)"
    by (simp add: the_lookup_eqvt[OF `x2 \<in> fdom m1`]  `x = _`)
  also have "... \<sqsubseteq> \<pi> \<bullet> (m2 f! x2)"
    by -(subst perm_cont_simp, rule fmap_belowE[OF `m1 \<sqsubseteq> m2`])
  also have "... \<sqsubseteq> (\<pi> \<bullet> m2) f! x"
    using `x = _`
    by (simp add: the_lookup_eqvt[OF `x2 \<in> fdom m2`]  )
  finally show "(\<pi> \<bullet> m1) f! x \<sqsubseteq> (\<pi> \<bullet> m2) f! x".

next
  fix \<pi> Y
  assume "chain (Y\<Colon>nat \<Rightarrow> 'a f\<rightharpoonup> 'b)" and  "chain (\<lambda>i. \<pi> \<bullet> Y i)"
  
  thus "fdom (\<pi> \<bullet> (\<Squnion> i. Y i)) = fdom (\<Squnion> i. \<pi> \<bullet> Y i)"
    by (metis chain_fdom(2) fdom_perm_rev)

  fix x
  assume "x \<in> fdom (\<pi> \<bullet> (\<Squnion> i. Y i))"
  moreover
  obtain x2 where "x = \<pi> \<bullet> x2" by (metis eqvt_bound)
  ultimately
  have "x2 \<in> fdom (\<Squnion> i. Y i)"
    using `x \<in> fdom (\<pi> \<bullet> (\<Squnion> i. Y i))` 
    by (simp add: fdom_perm mem_permute_iff del: fdom_perm_rev)+
  hence "x2 \<in> fdom (Y 0)"
    by (simp add: chain_fdom(2)[OF `chain Y`])
    
  have "\<pi> \<bullet> (\<Squnion> i. Y i) f! x = \<pi> \<bullet> ((\<Squnion> i. Y i) f! x2)"
    by (simp add: the_lookup_eqvt[OF `x2 \<in> fdom (\<Squnion> i. Y i)`]  `x = _`)
  also have "... = \<pi> \<bullet> (\<Squnion>i. (Y i f! x2))"
    by (subst lookup_cont[OF `chain Y`], rule refl)
  also have "... = (\<Squnion>i. \<pi> \<bullet> (Y i f! x2))"
    by (rule cont2contlubE[OF perm_cont, OF lookup_chain[OF `chain Y`]])
  also have "... = (\<Squnion>i. \<pi> \<bullet> Y i f! x)"
    using `x2 \<in> fdom (Y 0)` chain_fdom(1)[OF `chain Y`] `x = _`
    apply (subst the_lookup_eqvt)
    apply auto
    done
  also have "... = (\<Squnion>i. \<pi> \<bullet> Y i) f! x"
    by (subst lookup_cont[OF `chain (\<lambda>i. \<pi> \<bullet> Y i)`], rule refl)
  finally
  have "\<pi> \<bullet> (\<Squnion> i. Y i) f! x = (\<Squnion> i. \<pi> \<bullet> Y i) f! x" .
  thus "\<pi> \<bullet> (\<Squnion> i. Y i) f! x \<sqsubseteq> (\<Squnion> i. \<pi> \<bullet> Y i) f! x" by auto
qed

subsubsection {* Equivariance lemmas *}

lemma fmap_expand_eqvt[eqvt]:
  "\<pi> \<bullet> fmap_expand (m :: 'a::{pt} f\<rightharpoonup> 'b::{cont_pt,pcpo}) S = fmap_expand (\<pi> \<bullet> m) (\<pi> \<bullet> S)"
  by (transfer, perm_simp, rule refl)

end
