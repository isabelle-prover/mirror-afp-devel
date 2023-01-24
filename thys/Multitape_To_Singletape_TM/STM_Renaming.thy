section \<open>Renamings for Singletape Turing Machines\<close>

theory STM_Renaming
  imports 
    Singletape_TM
begin

locale renaming_of_singletape_tm = singletape_tm Q \<Sigma> \<Gamma> blank LE \<delta> s t r
  for Q :: "'q set" and \<Sigma> :: "'a set" and \<Gamma> blank LE \<delta> s t r
    + fixes ra :: "'a \<Rightarrow> 'b"    (* renaming of tape symbols *)
    and rq :: "'q \<Rightarrow> 'p"    (* renaming of states *)
  assumes ra: "inj_on ra \<Gamma>" 
    and rq: "inj_on rq Q" 
begin

abbreviation rd where "rd \<equiv> map_prod rq (map_prod ra (map_prod rq (map_prod ra (\<lambda> d :: dir. d))))"  

sublocale ren: singletape_tm "rq ` Q" "ra ` \<Sigma>" "ra ` \<Gamma>" "ra blank" "ra LE" "rd ` \<delta>" "rq s" "rq t" "rq r" 
proof (unfold_locales; (intro finite_imageI imageI image_mono fin_Q fin_\<Gamma> tm sQ tQ rQ)?)
  show "ra LE \<notin> ra ` \<Sigma>" using ra tm LE by (simp add: inj_on_image_mem_iff)
  show "ra blank \<notin> ra ` \<Sigma>" using ra tm blank by (simp add: inj_on_image_mem_iff)
  show "rq t \<noteq> rq r" using rq tQ rQ tr by (metis inj_on_contraD)
  show "rd ` \<delta> \<subseteq> (rq ` Q - {rq t, rq r}) \<times> ra ` \<Gamma> \<times> rq ` Q \<times> ra ` \<Gamma> \<times> UNIV" 
    using \<delta>_set tQ rQ rq by (auto simp: inj_on_def)
  fix p1 p2 b2 d
  assume "(p1, ra LE, p2, b2, d) \<in> rd ` \<delta>" 
  then obtain q1 q2 a1 a2 where mem: "(q1, a1, q2, a2, d) \<in> \<delta>" and 
    id: "p1 = rq q1" "ra LE = ra a1" "p2 = rq q2" "b2 = ra a2" by auto
  from \<delta>[OF mem] id(2) LE ra have "a1 = LE" by (simp add: inj_onD)
  with \<delta>LE[OF mem[unfolded this]]
  show "b2 = ra LE \<and> d \<in> {dir.N, dir.R}" unfolding id by auto
qed

fun rc :: "('a, 'q) st_config \<Rightarrow> ('b, 'p) st_config" where
  "rc (Config\<^sub>S q tc pos) = Config\<^sub>S (rq q) (ra o tc) pos" 

lemma ren_init: "rc (init_config w) = ren.init_config (map ra w)" 
  unfolding init_config_def ren.init_config_def rc.simps
  by auto

lemma ren_step: assumes "(c,c') \<in> step" 
  shows "(rc c, rc c') \<in> ren.step" 
  using assms
proof (cases rule: step.cases)
  case (step q ts n q' a dir)
  from step(3) have mem: "(rq q, ra (ts n), rq q', ra a, dir) \<in> rd ` \<delta>" by force
  show ?thesis unfolding step rc.simps
    by (intro ren.stepI[OF mem], auto)
qed

lemma ren_steps: assumes "(c,c') \<in> step^*" 
  shows "(rc c, rc c') \<in> ren.step^*" 
  using assms by (induct, insert ren_step, force+)

lemma ren_steps_count: assumes "(c,c') \<in> step^^n" 
  shows "(rc c, rc c') \<in> ren.step^^n" 
  using assms by (induct n arbitrary: c c', insert ren_step, force+)

lemma ren_Lang_forward: assumes "w \<in> Lang" 
  shows "map ra w \<in> ren.Lang" 
proof -
  from assms[unfolded Lang_def, simplified]
  obtain w' n where w: "set w \<subseteq> \<Sigma>" and steps: "(init_config w, Config\<^sub>S t w' n) \<in> step^*" 
    by auto
  from ren_steps[OF steps, unfolded ren_init, unfolded rc.simps] w
  show "map ra w \<in> ren.Lang" unfolding ren.Lang_def by auto
qed

abbreviation ira where "ira \<equiv> the_inv_into \<Gamma> ra" 
abbreviation irq where "irq \<equiv> the_inv_into Q rq"

interpretation inv: renaming_of_singletape_tm "rq ` Q" "ra ` \<Sigma>" "ra ` \<Gamma>" "ra blank" "ra LE" "rd ` \<delta>" "rq s" "rq t" "rq r" ira irq
  by (unfold_locales, insert ra rq inj_on_the_inv_into, auto)

lemmas inv_simps[simp] = the_inv_into_f_f[OF ra] the_inv_into_f_f[OF rq]

lemma inv_ren_Sigma: "ira ` ra ` \<Sigma> = \<Sigma>" using inv_simps(1)[OF set_mp[OF \<Sigma>_sub_\<Gamma>]]
  by (smt (verit, best) equalityI imageE image_subset_iff subsetI)

lemma inv_ren_Gamma: "ira ` ra ` \<Gamma> = \<Gamma>" using inv_simps(1)
  by (smt (verit, best) equalityI imageE image_subset_iff subsetI)

lemma inv_ren_t: "irq (rq t) = t" using tQ by simp
lemma inv_ren_s: "irq (rq s) = s" using sQ by simp
lemma inv_ren_r: "irq (rq r) = r" using rQ by simp
lemma inv_ren_blank: "ira (ra blank) = blank" using tm by simp
lemma inv_ren_LE: "ira (ra LE) = LE" using tm by simp

lemma inv_ren_\<delta>: "inv.rd ` rd ` \<delta> = \<delta>" 
proof -
  {
    fix trans :: "('q \<times> 'a \<times> 'q \<times> 'a \<times> dir)" 
    obtain q a p b d where trans: "trans = (q,a,p,b,d)" by (cases trans, auto)
    {
      assume t: "trans \<in> \<delta>" 
      note mem = \<delta>[OF this[unfolded trans]]
      from t have "inv.rd (rd trans) \<in> inv.rd ` rd ` \<delta>" by blast
      also have "inv.rd (rd trans) = trans" unfolding trans using mem by auto
      finally have "trans \<in> inv.rd ` rd ` \<delta>" .
    }
    moreover
    {
      assume t: "trans \<in> inv.rd ` rd ` \<delta>" 
      then obtain t' where t'd: "t' \<in> \<delta>" and tra: "trans = inv.rd (rd t')" by auto
      obtain q' a' p' b' d' where t': "t' = (q',a',p',b',d')" by (cases t', auto)
      note mem = \<delta>[OF t'd[unfolded t']]
      from tra[unfolded trans t'] mem
      have id: "q' = q" "a' = a" "p' = p" "b' = b" "d' = d" by auto
      with trans t'd t' have "trans \<in> \<delta>" by auto
    }
    ultimately have "trans \<in> inv.rd ` rd ` \<delta> \<longleftrightarrow> trans \<in> \<delta>" by blast
  }
  thus ?thesis by blast
qed

lemmas inv_ren = inv_ren_t inv_ren_s inv_ren_r inv_ren_\<delta> inv_ren_Gamma inv_ren_Sigma inv_ren_blank inv_ren_LE

lemma inv_ren_Lang: "inv.ren.Lang = Lang" unfolding inv_ren ..

lemma ren_Lang_backward: assumes "v \<in> ren.Lang" 
  shows "\<exists> w. v = map ra w \<and> w \<in> Lang" 
proof (intro exI conjI)
  let ?w = "map ira v" 
  from inv.ren_Lang_forward[OF assms, unfolded inv_ren_Lang]
  show "?w \<in> Lang" .
  show "v = map ra ?w" unfolding map_map o_def
  proof (subst map_idI)
    fix b
    assume "b \<in> set v" 
    with assms[unfolded ren.Lang_def] \<Sigma>_sub_\<Gamma> obtain a where a: "a \<in> \<Gamma>" and b: "b = ra a" by blast
    show "ra (ira b) = b" unfolding b using a by simp
  qed auto
qed

lemma ren_Lang: "ren.Lang = map ra ` Lang" 
proof
  show "map ra ` Lang \<subseteq> ren.Lang" using ren_Lang_forward by blast
  show "ren.Lang \<subseteq> map ra ` Lang" using ren_Lang_backward by blast
qed

lemma ren_det: assumes "deterministic" 
  shows "ren.deterministic" 
  unfolding ren.deterministic_def
proof (intro allI impI, goal_cases)
  case (1 q a p1 b1 d1 p2 b2 d2)
  let ?t1 = "(q, a, p1, b1, d1)"
  let ?t2 = "(q, a, p2, b2, d2)" 
  from 1 have t1: "inv.rd ?t1 \<in> inv.rd ` rd ` \<delta>" by force
  from 1 have t2: "inv.rd ?t2 \<in> inv.rd ` rd ` \<delta>" by force
  from t1 t2 have "(irq q, ira a, irq p1, ira b1, d1) \<in> \<delta>"  "(irq q, ira a, irq p2, ira b2, d2) \<in> \<delta>" 
    unfolding inv_ren by auto
  from assms[unfolded deterministic_def, rule_format, OF this]
  have id: "irq p1 = irq p2" "ira b1 = ira b2" and d: "d1 = d2" by auto
  from inj_onD[OF inv.rq id(1)] ren.\<delta>[OF 1(1)] ren.\<delta>[OF 1(2)]
  have p: "p1 = p2" by auto
  from inj_onD[OF inv.ra id(2)] ren.\<delta>[OF 1(1)] ren.\<delta>[OF 1(2)]
  have b: "b1 = b2" by auto
  show ?case unfolding b p d by simp
qed

lemma ren_upper_time: assumes "upper_time_bound f" 
  shows "ren.upper_time_bound f" 
  unfolding ren.upper_time_bound_def
proof (intro allI impI)
  fix w c n
  assume w: "set w \<subseteq> ra ` \<Sigma>" and steps: "(ren.init_config w, c) \<in> ren.step ^^ n" 
  define v where "v = map ira w" 
  from w have v: "set v \<subseteq> \<Sigma>" unfolding v_def
    using inv_ren_Sigma by fastforce
  from inv.ren_steps_count[OF steps]
  have "(inv.rc (ren.init_config w), inv.rc c) \<in> inv.ren.step ^^ n" .
  also have "inv.ren.step = step" using inv_ren_\<delta> by presburger
  also have "inv.rc (ren.init_config w) = init_config v" unfolding v_def using v w
    by (simp add: inv.ren_init inv_ren_LE inv_ren_blank inv_ren_s)
  finally have "(init_config v, inv.rc c) \<in> step ^^ n" .
  with assms[unfolded upper_time_bound_def] v have "n \<le> f (length v)" by simp
  thus "n \<le> f (length w)" unfolding v_def by auto
qed

end

lemma tm_renaming: assumes "valid_tm (tm :: ('q,'a)tm)" 
  and "inj_on (ra :: 'a \<Rightarrow> 'b) (\<Gamma>_tm tm)" 
  and "inj_on (rq :: 'q \<Rightarrow> 'p) (Q_tm tm)" 
shows "\<exists> tm' :: ('p,'b)tm. 
  valid_tm tm' \<and> 
  Lang_tm tm' = map ra ` Lang_tm tm \<and> 
  (det_tm tm \<longrightarrow> det_tm tm') \<and>
  (\<forall> f. upperb_time_tm tm f \<longrightarrow> upperb_time_tm tm' f)" 
proof (cases tm)
  case (TM Q \<Sigma> \<Gamma> bl le \<delta> s t r)
  with assms interpret singletape_tm Q \<Sigma> \<Gamma> bl le \<delta> s t r by auto
  interpret renaming_of_singletape_tm Q \<Sigma> \<Gamma> bl le \<delta> s t r ra rq
    by (unfold_locales, insert assms TM, auto)
  let ?tm' = "TM (rq ` Q) (ra ` \<Sigma>) (ra ` \<Gamma>) (ra bl) (ra le) (rd ` \<delta>) (rq s) (rq t) (rq r)" 
  show ?thesis
    by (rule exI[where x = ?tm'])
       (simp add: TM ren.singletape_tm_axioms ren_Lang ren_det ren_upper_time)
qed

end
