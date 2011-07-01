(*  Title:       Abstract Rewriting
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 Rene Thiemann       <rene.tiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and Rene Thiemann
    License:     LGPL
*)

(*
Copyright 2010 Christian Sternagel and René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

header {* Relative Rewriting *}

theory Relative_Rewriting
imports Abstract_Rewriting
begin

text {*Considering a relation @{term R} relative to another relation @{term S}, i.e.,
@{term R}-steps may be preceded and followd by arbitrary many @{term S}-steps.*}
abbreviation relto :: "('a * 'a) set \<Rightarrow> ('a * 'a) set \<Rightarrow> ('a * 'a) set" where
  "relto R S \<equiv> S^* O R O S^*"

definition SN_rel :: "'a ars \<Rightarrow> 'a ars \<Rightarrow> bool" where
  "SN_rel R S = (\<forall>(f::nat \<Rightarrow> 'a).
    (\<forall>i. (f i, f (Suc i)) \<in> R \<union> S) \<longrightarrow> (\<exists>i. \<forall>j \<ge> i. (f j, f (Suc j)) \<notin> R))"

lemma SN_relto_imp_SN_rel: "SN (relto R S) \<Longrightarrow> SN_rel R S"
proof -
  assume SN: "SN (relto R S)"
  show ?thesis
  proof (simp only: SN_rel_def, intro allI impI)
    fix f
    assume steps: "\<forall> i. (f i, f (Suc i)) \<in> R \<union> S"
    obtain r where  r: "\<And> j. r j \<equiv>  (f j, f (Suc j)) \<in> R" by auto
    show "\<exists> i. \<forall> j \<ge> i. (f j, f (Suc j)) \<notin> R"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence ih: "infinite_hits r" unfolding infinite_hits_def r by blast
      obtain r_index where "r_index = infinite_hits.index r" by simp
      with infinite_hits.index_p[OF ih] infinite_hits.index_ordered[OF ih] infinite_hits.index_not_p_between[OF ih] 
      have r_index: "\<And> i. r (r_index i) \<and> r_index i < r_index (Suc i) \<and> (\<forall> j. r_index i < j \<and> j < r_index (Suc i) \<longrightarrow> \<not> r j)" by auto
      obtain g where g: "\<And> i. g i \<equiv> f (r_index i)" ..
      {
        fix i
        let ?ri = "r_index i"
        let ?rsi = "r_index (Suc i)"
        from r_index have isi: "?ri < ?rsi" by auto
        obtain ri rsi where ri: "ri = ?ri" and rsi: "rsi = ?rsi" by auto
        with r_index[of i] steps have inter: "\<And> j. ri < j \<and> j < rsi \<Longrightarrow> (f j, f (Suc j)) \<in> S" unfolding r by auto
        from ri isi rsi have risi: "ri < rsi" by simp                      
        {
          fix n
          assume "Suc n \<le> rsi - ri"
          hence "(f (Suc ri), f (Suc (n + ri))) \<in> S^*"
          proof (induct n, simp)
            case (Suc n)
            hence stepps: "(f (Suc ri), f (Suc (n+ri))) \<in> S^*" by simp
            have "(f (Suc (n+ri)), f (Suc (Suc n + ri))) \<in> S"
              using inter[of "Suc n + ri"] Suc(2) by auto
            with stepps show ?case by simp
          qed
        }
        from this[of "rsi - ri - 1"] risi have 
          "(f (Suc ri), f rsi) \<in> S^*" by simp
        with ri rsi have ssteps: "(f (Suc ?ri), f ?rsi) \<in> S^*" by simp
        with r_index[of i] have "(f ?ri, f ?rsi) \<in> R O S^*" unfolding r by auto
        hence "(g i, g (Suc i)) \<in> S^* O R O S^*" using rtrancl_refl unfolding g by auto           
      } 
      hence "\<not> SN (S^* O R O S^*)" unfolding SN_defs by blast
      with SN show False by simp
    qed
  qed
qed

(*FIXME: move*)
lemma rtrancl_list_conv:
  "((s,t) \<in> R^*) = 
  (\<exists>list. last (s # list) = t \<and> (\<forall>i. i < length list \<longrightarrow> ((s # list) ! i, (s # list) ! Suc i) \<in> R))" (is "?l = ?r")
proof 
  assume ?r
  then obtain list where "last (s # list) = t \<and> (\<forall> i. i < length list \<longrightarrow> ((s # list) ! i, (s # list) ! Suc i) \<in> R)" ..
  thus ?l
  proof (induct list arbitrary: s, simp)
    case (Cons u ll)
    hence "last (u # ll) = t \<and> (\<forall> i. i < length ll \<longrightarrow> ((u # ll) ! i, (u # ll) ! Suc i) \<in> R)" by auto
    from Cons(1)[OF this] have rec: "(u,t) \<in> R^*" .
    from Cons have "(s, u) \<in> R" by auto
    with rec show ?case by auto
  qed
next
  assume ?l
  from rtrancl_imp_seq[OF this]
  obtain S n where s: "S 0 = s" and t: "S n = t" and steps: "\<forall> i<n. (S i, S (Suc i)) \<in> R" by auto
  let ?list = "map (\<lambda> i. S (Suc i)) [0 ..< n]"
  show ?r
  proof (rule exI[of _ ?list], intro conjI, 
      cases n, simp add: s[symmetric] t[symmetric], simp add: t[symmetric]) 
    show "\<forall> i < length ?list. ((s # ?list) ! i, (s # ?list) ! Suc i) \<in> R" 
    proof (intro allI impI)
      fix i
      assume i: "i < length ?list"
      thus "((s # ?list) ! i, (s # ?list) ! Suc i) \<in> R"
      proof (cases i, simp add: s[symmetric] steps)
        case (Suc j)
        with i steps show ?thesis by simp
      qed
    qed
  qed
qed

fun choice :: "(nat \<Rightarrow> 'a list) \<Rightarrow> nat \<Rightarrow> (nat \<times> nat)" where
  "choice f 0 = (0,0)"
| "choice f (Suc n) = (let (i, j) = choice f n in 
    if Suc j < length (f i) 
      then (i, Suc j)
      else (Suc i, 0))"
        
lemma SN_rel_imp_SN_relto : "SN_rel R S \<Longrightarrow> SN (relto R S)"
proof -
  assume SN: "SN_rel R S"
  show "SN (relto R S)"
  proof
    fix f
    assume  "\<forall> i. (f i, f (Suc i)) \<in> relto R S"
    hence steps: "\<And> i. (f i, f (Suc i)) \<in> S^* O R O S^*" by auto
    let ?prop = "\<lambda> i ai bi. (f i, bi) \<in> S^* \<and> (bi, ai) \<in> R \<and> (ai, f (Suc (i))) \<in> S^*"
    {
      fix i
      from steps obtain bi ai where "?prop i ai bi" by blast
      hence "\<exists> ai bi. ?prop i ai bi" by blast
    }
    hence "\<forall> i. \<exists> bi ai. ?prop i ai bi" by blast
    from choice[OF this] obtain b where "\<forall> i. \<exists> ai. ?prop i ai (b i)" by blast
    from choice[OF this] obtain a where steps: "\<And> i. ?prop i (a i) (b i)" by blast
    let ?prop = "\<lambda> i li. (b i, a i) \<in> R \<and> (\<forall> j < length li. ((a i # li) ! j, (a i # li) ! Suc j) \<in> S) \<and> last (a i # li) = b (Suc i)"
    {
      fix i
      from steps[of i] steps[of "Suc i"] have "(a i, f (Suc i)) \<in> S^*" and "(f (Suc i), b (Suc i)) \<in> S^*" by auto
      from rtrancl_trans[OF this] steps[of i] have R: "(b i, a i) \<in> R" and S: "(a i, b (Suc i)) \<in> S^*" by blast+
      from S[unfolded rtrancl_list_conv] obtain li where "last (a i # li) = b (Suc i) \<and> (\<forall> j < length li. ((a i # li) ! j, (a i # li) ! Suc j) \<in> S)" ..
      with R have "?prop i li" by blast
      hence "\<exists> li. ?prop i li" ..
    }
    hence "\<forall> i. \<exists> li. ?prop i li" ..
    from choice[OF this] obtain l where steps: "\<And> i. ?prop i (l i)" by auto
    let ?p = "\<lambda> i. ?prop i (l i)"
    from steps have steps: "\<And> i. ?p i" by blast
    let ?l = "\<lambda> i. a i # l i"
    let ?g = "\<lambda> i. choice (\<lambda> j. ?l j) i"
    obtain g where g: "\<And> i. g i = (let (ii,jj) = ?g i in ?l ii ! jj)" by auto
    have len: "\<And> i j n. ?g n = (i,j) \<Longrightarrow> j < length (?l i)"
    proof -
      fix i j n
      assume n: "?g n = (i,j)"
      show "j < length (?l i)" 
      proof (cases n)
        case 0
        with n have "j = 0" by auto
        thus ?thesis by simp
      next
        case (Suc nn)
        obtain ii jj where nn: "?g nn = (ii,jj)" by (cases "?g nn", auto)
        show ?thesis 
        proof (cases "Suc jj < length (?l ii)")
          case True
          with nn Suc have "?g n = (ii, Suc jj)" by auto
          with n True show ?thesis by simp
        next
          case False 
          with nn Suc have "?g n = (Suc ii, 0)" by auto
          with n show ?thesis by simp
        qed
      qed
    qed      
    have gsteps: "\<And> i. (g i, g (Suc i)) \<in> R \<union> S"
    proof -
      fix n
      obtain i j where n: "?g n = (i, j)" by (cases "?g n", auto)
      show "(g n, g (Suc n)) \<in> R \<union> S"
      proof (cases "Suc j < length (?l i)")
        case True
        with n have "?g (Suc n) = (i, Suc j)" by auto
        with n have gn: "g n = ?l i ! j" and gsn: "g (Suc n) = ?l i ! (Suc j)" unfolding g by auto
        thus ?thesis using steps[of i] True by auto
      next
        case False
        with n have "?g (Suc n) = (Suc i, 0)" by auto
        with n have gn: "g n = ?l i ! j" and gsn: "g (Suc n) = a (Suc i)" unfolding g by auto
        from gn len[OF n] False have "j = length (?l i) - 1" by auto
        with gn have gn: "g n = last (?l i)" using last_conv_nth[of "?l i"] by auto
        from gn gsn show ?thesis using steps[of i] steps[of "Suc i"] by auto
      qed
    qed
    have infR:  "\<forall> n. \<exists> j \<ge> n. (g j, g (Suc j)) \<in> R" 
    proof
      fix n
      obtain i j where n: "?g n = (i,j)" by (cases "?g n", auto)
      from len[OF n] have j: "j \<le> length (?l i) - 1" by simp
      let ?k = "length (?l i) - 1 - j"
      obtain k where k: "k = j + ?k" by auto
      from j k have k2: "k = length (?l i) - 1" and k3: "j + ?k < length (?l i)" by auto
      {
        fix n i j k l
        assume n: "choice l n = (i,j)" and "j + k < length (l i)"
        hence "choice l (n + k) = (i, j + k)"
          by (induct k arbitrary: j, simp, auto)
      }
      from this[OF n, of ?k, OF k3]
      have gnk: "?g (n + ?k) = (i, k)" by (simp only: k)
      hence "g (n + ?k) = ?l i ! k" unfolding g by auto
      hence gnk2: "g (n + ?k) = last (?l i)" using last_conv_nth[of "?l i"] k2 by auto
      from k2 gnk have "?g (Suc (n+?k)) = (Suc i, 0)" by auto
      hence gnsk2: "g (Suc (n+?k)) = a (Suc i)" unfolding g by auto
      from steps[of i] steps[of "Suc i"] have main: "(g (n+?k), g (Suc (n+?k))) \<in> R" 
        by (simp only: gnk2 gnsk2)
      show "\<exists> j \<ge> n. (g j, g (Suc j)) \<in> R" 
        by (rule exI[of _ "n + ?k"], auto simp: main[simplified])
    qed      
    from SN[simplified SN_rel_def] gsteps infR show False by blast
  qed
qed

hide_const choice

lemma SN_relto_SN_rel_conv: "SN (relto R S) = SN_rel R S"
  by (blast intro: SN_relto_imp_SN_rel SN_rel_imp_SN_relto)

lemma SN_rel_empty1: "SN_rel {} S"
  unfolding SN_rel_def by auto

lemma SN_rel_empty2: "SN_rel R {} = SN R"
  unfolding SN_rel_def SN_defs by auto

lemma relto_mono:
  assumes "R \<subseteq> R'" and "S \<subseteq> S'"
  shows "relto R S \<subseteq> relto R' S'"
  using assms rtrancl_mono by blast

lemma SN_relto_mono:
  assumes R: "R \<subseteq> R'" and S: "S \<subseteq> S'"
  and SN: "SN (relto R' S')"
  shows "SN (relto R S)"
  using SN SN_subset[OF _ relto_mono[OF R S]] by blast

lemmas SN_rel_mono = SN_relto_mono[unfolded SN_relto_SN_rel_conv]

lemma SN_relto_imp_SN:
  assumes "SN (relto R S)" shows "SN R"
proof
  fix f
  assume "\<forall>i. (f i, f (Suc i)) \<in> R"
  hence "\<And>i. (f i, f (Suc i)) \<in> relto R S" by blast
  thus False using assms unfolding SN_defs by force
qed

lemma relto_trancl_conv: "(relto R S)^+ = ((R \<union> S))^* O R O ((R \<union> S))^*" (is "_ = ?RS^* O ?R O _")
proof
  show "?RS^* O ?R O ?RS^* \<subseteq> (relto R S)^+"
  proof(clarify, simp)
    fix x1 x2 x3 x4
    assume x12: "(x1,x2) \<in> ((R \<union> S))^*" and x23: "(x2,x3) \<in> R" and x34: "(x3,x4) \<in> ((R \<union> S))^*"
    let ?S = "S^*"
    {
      fix x y z
      assume "(y,z) \<in> ((R \<union> S))^*"
      hence "(x,y) \<in> relto R S \<longrightarrow> (x,z) \<in> (relto R S)^+"
      proof (induct)
        case base
        show ?case by auto
      next
        case (step u z)
        show ?case
        proof
          assume "(x,y) \<in> relto R S"
          with step have nearly: "(x,u) \<in> (relto R S)^+" by simp
          from step(2)
          show "(x,z) \<in> (relto R S)^+"
          proof
            assume "(u,z) \<in> R"
            hence "(u,z) \<in> relto R S" by auto
            with nearly show ?thesis by auto
          next
            assume uz: "(u,z) \<in> S"
            from nearly[unfolded trancl_unfold_right]
            obtain v where xv: "(x,v) \<in> (relto R S)^*" and vu: "(v,u) \<in> relto R S" by auto
            from vu obtain w where vw: "(v,w) \<in> ?S O R" and wu: "(w,u) \<in> ?S" by auto
            from wu uz have wz: "(w,z) \<in> ?S" by auto
            with vw have vz: "(v,z) \<in> relto R S" by auto
            with xv show ?thesis by auto
          qed
        qed
      qed
    } note steps_right = this
    from x23 have "(x2,x3) \<in> relto R S" by auto
    from mp[OF steps_right[OF x34] this] have x24: "(x2,x4) \<in> (relto R S)^+" .
    with x12 show "(x1,x4) \<in> (relto R S)^+" 
    proof (induct arbitrary: x4, simp)
      case (step y z) 
      from step(2)
      have "(y,x4) \<in> (relto R S)^+"
      proof
        assume "(y,z) \<in> R"
        hence "(y,z) \<in> relto R S" by auto
        with step(4) show ?thesis by auto
      next
        assume yz: "(y,z) \<in> S"
        from step(4)[unfolded trancl_unfold_left]
        obtain v where zv: "(z,v) \<in> relto R S" and vx4: "(v,x4) \<in> (relto R S)^*" by auto
        from zv obtain w where zw: "(z,w) \<in> ?S" and wv: "(w,v) \<in> R O ?S" by auto
        from yz zw have "(y,w) \<in> ?S" by auto
        with wv have "(y,v) \<in> relto R S" by auto
        with vx4 show ?thesis by auto
      qed
      from step(3)[OF this] show ?case .
    qed
  qed 
next
  have S: "S^* \<subseteq> ?RS^*" by (rule rtrancl_mono[of S "R \<union> S", simplified])
  have R: "R \<subseteq> ?RS^*" by auto
  show "(relto R S)^+ \<subseteq> ?RS^* O ?R O ?RS^*"
  proof
    fix x y
    assume "(x,y) \<in> (S^* O R O S^*)^+"
    thus "(x,y) \<in> ?RS^* O ?R O ?RS^*"
    proof (induct)
      case (base y)
      thus ?case using S by blast 
    next
      case (step y z)
      from step(2) have "(y,z) \<in> ?RS^* O ?RS^* O ?RS^*" using R S by blast
      hence "(y,z) \<in> ?RS^*" by auto
      with step (3) show ?case by force
    qed
  qed
qed

lemma relto_Id: "relto R (S \<union> Id) = relto R S"
  by simp

lemma SN_relto_Id:
  "SN (relto R (S \<union> Id)) = SN (relto R S)"
  by (simp only: relto_Id)

end