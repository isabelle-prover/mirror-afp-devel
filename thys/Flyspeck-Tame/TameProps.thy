(* ID:         $Id: TameProps.thy,v 1.3 2007-07-11 10:12:00 stefanberghofer Exp $
   Author:     Tobias Nipkow
*)

header{* Tame Properties *}

theory TameProps
imports Tame RTranCl
begin


lemma length_disj_filter_le: "\<forall>x \<in> set xs. \<not>(P x \<and> Q x) \<Longrightarrow>
 length(filter P xs) + length(filter Q xs) \<le> length xs"
by(induct xs) auto

lemma tri_quad_le_degree: "tri g v + quad g v \<le> degree g v"
proof -
  let ?fins = "[f \<leftarrow> facesAt g v . final f]"
  have "tri g v + quad g v =
        |[f \<leftarrow> ?fins . triangle f]| + |[f \<leftarrow> ?fins. |vertices f| = 4]|"
    by(simp add:tri_def quad_def)
  also have "\<dots> \<le> |[f \<leftarrow> facesAt g v. final f]|"
    by(rule length_disj_filter_le) simp
  also have "\<dots> \<le> |facesAt g v|" by(rule length_filter_le)
  finally show ?thesis by(simp add:degree_def)
qed

lemma faceCountMax_bound:
 "\<lbrakk> tame g; v \<in> \<V> g \<rbrakk> \<Longrightarrow> tri g v + quad g v \<le> 6"
using tri_quad_le_degree[of g v]
by(auto simp:tame_def tame\<^isub>4\<^isub>5_def split:split_if_asm)


lemma filter_tame_succs:
assumes invP: "invariant P succs" and fin: "!!g. final g \<Longrightarrow> succs g = []"
and ok_untame: "!!g. P g \<Longrightarrow> \<not> ok g \<Longrightarrow> final g \<and> \<not> tame g"
and gg': "g [succs]\<rightarrow>* g'"
shows "P g \<Longrightarrow> final g' \<Longrightarrow> tame g' \<Longrightarrow> g [filter ok o succs]\<rightarrow>* g'"
using gg'
proof (induct rule:RTranCl.induct)
  case refl show ?case by(rule RTranCl.refl)
next
  case (succs h' h h'')
  hence "P h'"  using invP by(unfold invariant_def) blast
  show ?case
  proof cases
    assume "ok h'"
    thus ?thesis using succs `P h'` by(fastsimp intro:RTranCl.succs)
  next
    assume "\<not> ok h'" note fin_tame = ok_untame[OF `P h'` `\<not> ok h'`]
    have "h'' = h'" using fin_tame
      by(rule_tac RTranCl.cases[OF succs(2)])(auto simp:fin)
    hence False using fin_tame succs by fast
    thus ?case ..
  qed
qed


constdefs
 untame :: "(graph \<Rightarrow> bool) \<Rightarrow> bool"
"untame P \<equiv> \<forall>g. final g \<and> P g \<longrightarrow> \<not> tame g"


lemma filterout_untame_succs:
assumes invP: "invariant P f" and invPU: "invariant (%g. P g \<and>  U g) f"
and untame: "untame(%g. P g \<and> U g)"
and new_untame: "!!g g'. \<lbrakk> P g; g' \<in> set(f g); g' \<notin> set(f' g) \<rbrakk> \<Longrightarrow> U g'"
and gg': "g [f]\<rightarrow>* g'"
shows "P g \<Longrightarrow> final g' \<Longrightarrow> tame g' \<Longrightarrow> g [f']\<rightarrow>* g'"
using gg'
proof (induct rule:RTranCl.induct)
  case refl show ?case by(rule RTranCl.refl)
next
  case (succs h' h h'')
  hence Ph': "P h'"  using invP by(unfold invariant_def) blast
  show ?case
  proof cases
    assume "h' \<in> set(f' h)"
    thus ?thesis using succs Ph' by(blast intro:RTranCl.succs)
  next
    assume "h' \<notin> set(f' h)"
    with succs(4) succs(1) have "U h'" by (rule new_untame)
    hence False using Ph' RTranCl_inv[OF invPU] untame succs
      by (unfold untame_def) fast
    thus ?case ..
  qed
qed


lemma comp_map_tame_pres:
assumes invP: "invariant P succs"
and invPU: "invariant (%g. P g \<and> U g) succs" and untame: "untame U"
and f_fin: "!!g. final g \<Longrightarrow> f g = g"
and invPUf: "invariant (%g. P g \<and> U g) (%g. [f g])"
and succs_f: "!!g\<^isub>0 g g'. P g\<^isub>0 \<Longrightarrow> g \<in> set(succs g\<^isub>0) \<Longrightarrow> g' \<in> set(succs g) \<Longrightarrow>
              U g' \<or> f g = g \<or> f g' = f g"
and gg': "g [succs]\<rightarrow>* g'"
shows "P g \<Longrightarrow> final g' \<Longrightarrow> tame g' \<Longrightarrow> g [map f o succs]\<rightarrow>* g'"
using gg'
proof (induct rule:RTranCl.induct)
  case refl show ?case by(rule RTranCl.refl)
next
  case (succs h' h h'')
  hence Ph': "P h'" using invP by(unfold invariant_def) blast
  hence IH: "h' [map f \<circ> succs]\<rightarrow>* h''" using succs by blast
  thus ?case
  proof (rule RTranCl_elim)
    assume "h'' = h'"
    moreover hence "f h' = h'" using f_fin[OF succs(5)] by simp
    ultimately show ?case using succs(1)
      by(force intro!: RTranCl.succs[OF _ RTranCl.refl])
  next
    fix h\<^isub>2
    assume 1: "h' [map f \<circ> succs]\<rightarrow> h\<^isub>2" and
           2: "h\<^isub>2 [map f \<circ> succs]\<rightarrow>* h''"
    from 1 obtain h\<^isub>1 where h\<^isub>1: "h\<^isub>1 \<in> set(succs h')" and [simp]: "h\<^isub>2 = f h\<^isub>1"
      by force
    { assume Uh\<^isub>1: "U h\<^isub>1"
      have invPU2: "invariant (%g. P g \<and> U g) (map f o succs)"
	using invPU invPUf by(auto simp:invariant_def)
      have Ph\<^isub>1: "P h\<^isub>1" using succs(1) succs(4) h\<^isub>1 invP
	by(unfold invariant_def) blast
      have PUh\<^isub>2: "P h\<^isub>2 \<and> U h\<^isub>2" using invariantE[OF invPUf] Ph\<^isub>1 Uh\<^isub>1 by auto
      from RTranCl_inv[OF invPU2 2, OF PUh\<^isub>2]
      have False using succs(5-6) untame by(auto simp:untame_def)
      hence ?thesis ..
    } moreover
    { assume "f h' = h'"
      hence "h' \<in> set((map f o succs) h)" using succs(1) by force
      hence ?thesis using IH by(rule RTranCl.succs)
    } moreover
    { assume ff: "f h\<^isub>1 = f h'"
      hence "h\<^isub>2 \<in> set((map f o succs) h)" using succs(1) by auto
      hence ?thesis using 2 by(rule RTranCl.succs)
    }
    ultimately show ?thesis using succs_f[OF succs(4) succs(1) h\<^isub>1] by blast
  qed
qed

end
