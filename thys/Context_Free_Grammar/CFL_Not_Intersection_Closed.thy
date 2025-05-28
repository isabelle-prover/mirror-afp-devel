(*
Authors: Felix Krayer, Tobias Nipkow
*)

section "CFLs Are Not Closed Under Intersection"

theory CFL_Not_Intersection_Closed
imports
  "List_Power.List_Power"
  Context_Free_Language
  Pumping_Lemma_CFG
  AnBnCn_not_CFL
begin

text \<open>The probably first formal proof was given by Ramos \emph{et al.} \<^cite>\<open>RamosAMQ and RamosGithub\<close>.
The proof below is much shorter.\<close>

text "Some lemmas:"

(* TODO: rm with next release because def of (@@) is now as below: *)
lemma Lang_concat:
  "L1 @@ L2 = {word. \<exists>w1 \<in> L1. \<exists>w2 \<in> L2. word = w1 @ w2}"
  unfolding conc_def by blast

lemma deriven_same_repl:
  assumes "(A, u' @ [Nt A] @ v') \<in> P"
  shows "P \<turnstile> u @ [Nt A] @ v \<Rightarrow>(n) u @ (u'^^n) @ [Nt A] @ (v'^^n) @ v"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "P \<turnstile> u @ (u'^^n) @ [Nt A] @ (v'^^n) @ v \<Rightarrow> u @ (u'^^n) @ u' @ [Nt A] @ v' @ (v'^^n) @ v" 
    using assms derive.intros[of _ _ _ "u @ (u'^^n)" "(v'^^n) @ v"] by fastforce 
  then have "P \<turnstile> u @ (u'^^n) @ [Nt A] @ (v'^^n) @ v \<Rightarrow> u @ (u'^^(Suc n)) @ [Nt A] @ (v'^^(Suc n)) @ v"
    by (metis append.assoc pow_list_Suc2 pow_list_comm) 
  then show ?case using Suc by auto
qed


text "Now the main proof."

lemma an_CFL: "CFL TYPE('n) (\<Union>n. {[a]^^n})" (is "CFL _ ?L")
proof  -
  obtain P X where P_def: "(P::('n, 'a) Prods) = {(X, [Tm a, Nt X]), (X, [])}" by simp
  have "Lang P X = ?L" 
  proof
    show "Lang P X \<subseteq> ?L" 
    proof
      fix w
      assume "w \<in> Lang P X"
      then have "P \<turnstile> [Nt X] \<Rightarrow>* map Tm w" using Lang_def by fastforce
      then have "\<exists>n. map Tm w = ([Tm a]^^n) @ [Nt X] \<or> (map Tm w::('n, 'a)syms) = ([Tm a]^^n)"
      proof(induction rule: derives_induct)
        case base
        then show ?case by (auto simp: pow_list_single_Nil_iff)
      next
        case (step u A v w')
        then have "A=X" using P_def by auto
        have "P \<turnstile> u @ [Nt X] @ v \<Rightarrow> u @ w' @ v" using \<open>A=X\<close> derive.intros step by fast
        obtain n where n_src: "u @ [Nt X] @ v = ([Tm a]^^n) @ [Nt X] \<or> u @ [Nt X] @ v = ([Tm a]^^n)" 
          using \<open>A=X\<close> step by auto 
        have notin: "Nt X \<notin> set ([Tm a]^^n)" by (simp add: pow_list_single)
        then have "u @ [Nt X] @ v = ([Tm a]^^n) @ [Nt X]" 
          using n_src append_Cons in_set_conv_decomp by metis
        then have uv_eq: "u = ([Tm a]^^n) \<and> v = []" 
          using notin n_src Cons_eq_appendI append_Cons_eq_iff append_Nil in_set_insert insert_Nil snoc_eq_iff_butlast by metis
        have "w' = [Tm a, Nt X] \<or> w' = []" using step(2) P_def by auto
        then show ?case
        proof
          assume "w' = [Tm a, Nt X]"
          then have "u @ w' @ v = ([Tm a]^^(Suc n)) @ [Nt X]" using uv_eq by (simp add: pow_list_comm)
          then show ?case by blast
        next
          assume "w' = []"
          then show ?case using uv_eq by blast
        qed
      qed
      then obtain n' where n'_src: "(map Tm w) = ([Tm a]^^n') @ [Nt X] \<or> ((map Tm w)::('n, 'a)syms) = ([Tm a]^^n')" by auto
      have "Nt X \<notin> set (map Tm w)" by auto
      then have "((map Tm w)::('n, 'a)syms) = ([Tm a]^^n')" using n'_src by fastforce
      have "map Tm ([a]^^n') = ([Tm a]^^n')" by (simp add: map_concat)
      then have "w = [a]^^n'" using \<open>map Tm w = ([Tm a]^^n')\<close> by (metis list.inj_map_strong sym.inject(2))
      then show "w \<in> ?L" by auto
    qed
  next
    show "?L \<subseteq> Lang P X" 
    proof
      fix w
      assume "w \<in> ?L"
      then obtain n where n_src: "w = [a]^^n" by blast
      (*"X \<Rightarrow>* a^n"*)
      have Xa: "P \<turnstile> [Nt X] \<Rightarrow>(n) ([Tm a]^^n) @ [Nt X]"
        using P_def deriven_same_repl[of "X" "[Tm a]" "[]" _ _ "[]" ] by (simp add: pow_list_Nil)
      have X\<epsilon>: "P \<turnstile> ([Tm a]^^n) @ [Nt X] \<Rightarrow> ([Tm a]^^n)" using P_def derive.intros[of "X" "[]" _ "[Tm a]^^n" "[]"] by auto
      have "([Tm a]^^n) = map Tm w" using n_src by auto
      then have "P \<turnstile> [Nt X] \<Rightarrow>* map Tm w" using Xa X\<epsilon> relpowp_imp_rtranclp
        by (smt (verit, best) rtranclp.simps) 
      then show "w \<in> Lang P X" using Lang_def by fastforce
    qed
  qed
  then show ?thesis unfolding CFL_def P_def by blast
qed

lemma anbn_CFL: "CFL TYPE('n) (\<Union>n. {[a]^^n @ [b]^^n})" (is "CFL _ ?L")
proof  -
  obtain P X where P_def: "(P::('n, 'a) Prods) = {(X, [Tm a, Nt X, Tm b]), (X, [])}" by simp
  let ?G = "Cfg P X"
  have "Lang P X = ?L" 
  proof
    show "Lang P X \<subseteq> ?L" proof
      fix w
      assume "w \<in> Lang P X"
      then have "P \<turnstile> [Nt X] \<Rightarrow>* map Tm w" using Lang_def by fastforce
      then have "\<exists>n. map Tm w = ([Tm a]^^n) @ [Nt X] @ ([Tm b]^^n) \<or> (map Tm w::('n, 'a)syms) = ([Tm a]^^n) @ ([Tm b]^^n)"
      proof(induction rule: derives_induct)
        case base
        have "[Nt X] = ([Tm a]^^0) @ [Nt X] @ ([Tm b]^^0)" by auto
        then show ?case by fast
      next
        case (step u A v w')
        then have "A=X" using P_def by auto
        have "P \<turnstile> u @ [Nt X] @ v \<Rightarrow> u @ w' @ v" using \<open>A=X\<close> derive.intros step by fast
        obtain n where n_src: "u @ [Nt X] @ v = ([Tm a]^^n) @ [Nt X] @ ([Tm b]^^n) \<or> u @ [Nt X] @ v = ([Tm a]^^n) @ ([Tm b]^^n)" 
          using \<open>A=X\<close> step by auto
        have notin2: "Nt X \<notin> set ([Tm a]^^n) \<and> Nt X \<notin> set ([Tm b]^^n)"
          by (simp add: pow_list_single)
        then have notin: "Nt X \<notin> set (([Tm a]^^n) @ ([Tm b]^^n))" by simp
        then have uv_split: "u @ [Nt X] @ v = ([Tm a]^^n) @ [Nt X] @ ([Tm b]^^n)" 
          by (metis n_src append_Cons in_set_conv_decomp)
        have u_eq: "u = ([Tm a]^^n)"
          by (metis (no_types, lifting) uv_split notin2 Cons_eq_appendI append_Cons_eq_iff eq_Nil_appendI) 
        then have v_eq: "v = ([Tm b]^^n)" 
           by (metis (no_types, lifting) uv_split notin2 Cons_eq_appendI append_Cons_eq_iff eq_Nil_appendI)
        have "w' = [Tm a, Nt X, Tm b] \<or> w' = []" using step(2) P_def by auto
        then show ?case
        proof
          assume "w' = [Tm a, Nt X, Tm b]"
          then have "u @ w' @ v = ([Tm a]^^n) @ [Tm a, Nt X, Tm b] @ ([Tm b]^^n)" using u_eq v_eq by simp
          then have "u @ w' @ v = ([Tm a]^^(Suc n)) @ [Nt X] @ ([Tm b]^^(Suc n)) "
            by (simp add: pow_list_comm)
          then show ?case by blast
        next
          assume "w' = []"
          then show ?case using u_eq v_eq by blast
        qed
      qed
      then obtain n' where n'_src: "(map Tm w) = ([Tm a]^^n') @ [Nt X] @ ([Tm b]^^n') \<or> ((map Tm w)::('n, 'a)syms) = ([Tm a]^^n') @ ([Tm b]^^n')" by auto
      have "Nt X \<notin> set (map Tm w)" by auto
      then have w_ab: "((map Tm w)::('n, 'a)syms) = ([Tm a]^^n') @ ([Tm b]^^n')" using n'_src by fastforce
      have map_a: "([Tm a]^^n') = map Tm ([a]^^n')" by (simp add: map_concat)
      have map_b: "([Tm b]^^n') = map Tm ([b]^^n')" by (simp add: map_concat)
      from w_ab map_a map_b have "((map Tm w)::('n, 'a)syms) = map Tm ([a]^^n') @  map Tm ([b]^^n')" by metis
      then have "((map Tm w)::('n, 'a)syms) = map Tm (([a]^^n') @ ([b]^^n'))" by simp
      then have "w = [a]^^n' @ [b]^^n'" by (metis list.inj_map_strong sym.inject(2))
      then show "w \<in> ?L" by auto
    qed
  next
    show "?L \<subseteq> Lang P X" 
    proof
      fix w
      assume "w \<in> ?L"
      then obtain n where n_src: "w = [a]^^n @ [b]^^n" by blast
      (*"X \<Rightarrow>* a^nb^n"*)
      have Xa: "P \<turnstile> [Nt X] \<Rightarrow>(n) ([Tm a]^^n) @ [Nt X] @ ([Tm b]^^n)"
        using P_def deriven_same_repl[of "X" "[Tm a]" "[Tm b]" _ _ "[]" "[]"] by simp
      have X\<epsilon>: "P \<turnstile> ([Tm a]^^n) @ [Nt X] @ ([Tm b]^^n) \<Rightarrow> ([Tm a]^^n) @ ([Tm b]^^n)" 
        using P_def derive.intros[of "X" "[]" _ "[Tm a]^^n" "[Tm b]^^n"] by auto
      have "[Tm a]^^n @ [Tm b]^^n = map Tm ([a]^^n) @ (map Tm ([b]^^n))" by simp
      then have "([Tm a]^^n) @ ([Tm b]^^n) = map Tm w" using n_src by simp
      then have "P \<turnstile> [Nt X] \<Rightarrow>* map Tm w" using Xa X\<epsilon> relpowp_imp_rtranclp
        by (smt (verit, best) rtranclp.simps) 
      then show "w \<in> Lang P X" using Lang_def by fastforce
    qed
  qed
  then show ?thesis unfolding CFL_def P_def by blast
qed

lemma intersection_anbncn: 
  assumes "a\<noteq>b" "b\<noteq>c" "c\<noteq>a"
  and "\<exists>x y z. w = [a]^^x@[b]^^y@[c]^^z \<and> x = y"
  and "\<exists>x y z. w = [a]^^x@[b]^^y@[c]^^z \<and> y = z"
  shows "\<exists>x y z. w = [a]^^x@[b]^^y@[c]^^z \<and> x = y \<and> y = z"
proof -
  obtain x1 y1 z1 where src1: "w = [a]^^x1@[b]^^y1@[c]^^z1 \<and> x1 = y1" using assms by blast
  obtain x2 y2 z2 where src2: "w = [a]^^x2@[b]^^y2@[c]^^z2 \<and> y2 = z2" using assms by blast
  have "[a]^^x1@[b]^^y1@[c]^^z1 = [a]^^x2@[b]^^y2@[c]^^z2" using src1 src2 by simp
  have cx1: "count_list w a = x1" using src1 assms by (simp)
  have cx2: "count_list w a = x2" using src2 assms by (simp)
  from cx1 cx2 have eqx: "x1 = x2" by simp

  have cy1: "count_list w b = y1" using assms src1 by (simp)
  have cy2: "count_list w b = y2" using assms src2 by simp
  from cy1 cy2 have eqy: "y1 = y2" by simp

  have cz1: "count_list w c = z1" using assms src1 by simp
  have cz2: "count_list w c = z2" using assms src2 by simp
  from cz1 cz2 have eqz: "z1 = z2" by simp

  have "w = [a]^^x1@[b]^^y1@[c]^^z1 \<and> x1 = y1 \<and> y1 = z1" using eqx eqy eqz src1 src2 by blast
  then show ?thesis by blast
qed

lemma CFL_intersection_not_closed:
  fixes a b c :: 'a
  assumes "a\<noteq>b" "b\<noteq>c" "c\<noteq>a"
  shows "\<exists>L1 L2 :: 'a list set.
    CFL TYPE(('n1 + 'n1) option) L1 \<and> CFL TYPE(('n2 + 'n2) option) L2
 \<and> (\<nexists>(P::('x::infinite,'a)Prods) S. Lang P S = L1 \<inter> L2 \<and> finite P)"
proof -
  let ?anbn = "\<Union>n. {[a]^^n @ [b]^^n}"
  let ?cm = "\<Union>n. {[c]^^n}"
  let ?an = "\<Union>n. {[a]^^n}"
  let ?bmcm = "\<Union>n. {[b]^^n @ [c]^^n}"
  let ?anbncm = "\<Union>n. \<Union>m. {[a]^^n @ [b]^^n @ [c]^^m}"
  let ?anbmcm = "\<Union>n. \<Union>m. {[a]^^n @ [b]^^m @ [c]^^m}"
  have anbn: "CFL TYPE('n1) ?anbn" by(rule anbn_CFL)
  have cm: "CFL TYPE('n1) ?cm" by(rule an_CFL)
  have an: "CFL TYPE('n2) ?an" by(rule an_CFL)
  have bmcm: "CFL TYPE('n2) ?bmcm" by(rule anbn_CFL)
  have "?anbncm = ?anbn @@ ?cm" unfolding Lang_concat by auto
  then have anbncm: "CFL TYPE(('n1 + 'n1) option) ?anbncm" using anbn cm CFL_concat_closed by auto
  have "?anbmcm = ?an @@ ?bmcm" unfolding Lang_concat by auto
  then have anbmcm: "CFL TYPE(('n2 + 'n2) option) ?anbmcm" using an bmcm CFL_concat_closed by auto
  have "?anbncm \<inter> ?anbmcm = (\<Union> n. {[a]^^n@[b]^^n@[c]^^n})" 
    using intersection_anbncn[OF assms] by auto
  then have "CFL TYPE(('n1 + 'n1) option) ?anbncm \<and> 
        CFL TYPE(('n2 + 'n2) option) ?anbmcm \<and> 
        (\<nexists>P::('x,'a)Prods.\<exists>S. Lang P S = ?anbncm \<inter> ?anbmcm \<and> finite P)" 
    using  anbncn_not_cfl[OF assms, where 'n = 'x] anbncm anbmcm by auto
  then show ?thesis by auto
qed

end