(*  Title:   Binary_CoProduct_QuasiBorel.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

subsection \<open>Coproduct Spaces\<close>

theory Binary_CoProduct_QuasiBorel
  imports "Measure_QuasiBorel_Adjunction"
begin

subsubsection \<open> Binary Coproduct Spaces  \<close>
definition copair_qbs_Mx :: "['a quasi_borel, 'b quasi_borel] \<Rightarrow> (real => 'a + 'b) set" where
"copair_qbs_Mx X Y \<equiv> 
  {g. \<exists> S \<in> sets real_borel.
  (S = {}   \<longrightarrow> (\<exists> \<alpha>1\<in> qbs_Mx X. g = (\<lambda>r. Inl (\<alpha>1 r)))) \<and>
  (S = UNIV \<longrightarrow> (\<exists> \<alpha>2\<in> qbs_Mx Y. g = (\<lambda>r. Inr (\<alpha>2 r)))) \<and>
  ((S \<noteq> {} \<and> S \<noteq> UNIV) \<longrightarrow>
     (\<exists> \<alpha>1\<in> qbs_Mx X.
      \<exists> \<alpha>2\<in> qbs_Mx Y.
          g = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))))}"


definition copair_qbs :: "['a quasi_borel, 'b quasi_borel] \<Rightarrow> ('a + 'b) quasi_borel" (infixr "<+>\<^sub>Q" 65) where
"copair_qbs X Y \<equiv> Abs_quasi_borel (qbs_space X <+> qbs_space Y, copair_qbs_Mx X Y)"


text \<open> The followin is an equivalent definition of @{term copair_qbs_Mx}. \<close>
definition copair_qbs_Mx2 :: "['a quasi_borel, 'b quasi_borel] \<Rightarrow> (real => 'a + 'b) set" where
"copair_qbs_Mx2 X Y \<equiv> 
  {g. (if qbs_space X = {} \<and> qbs_space Y = {} then False
       else if qbs_space X \<noteq> {} \<and> qbs_space Y = {} then 
                  (\<exists>\<alpha>1\<in> qbs_Mx X. g = (\<lambda>r. Inl (\<alpha>1 r)))
       else if qbs_space X = {} \<and> qbs_space Y \<noteq> {} then 
                  (\<exists>\<alpha>2\<in> qbs_Mx Y. g = (\<lambda>r. Inr (\<alpha>2 r)))
       else 
         (\<exists>S \<in> sets real_borel. \<exists>\<alpha>1\<in> qbs_Mx X. \<exists>\<alpha>2\<in> qbs_Mx Y.
          g = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r))))) }"

lemma copair_qbs_Mx_equiv :"copair_qbs_Mx (X :: 'a quasi_borel) (Y :: 'b quasi_borel) = copair_qbs_Mx2 X Y"
proof(auto)
(* \<subseteq> *)
  fix g :: "real \<Rightarrow> 'a + 'b"
  assume "g \<in> copair_qbs_Mx X Y"
  then obtain S where hs:"S\<in> sets real_borel \<and> 
  (S = {}   \<longrightarrow> (\<exists> \<alpha>1\<in> qbs_Mx X. g = (\<lambda>r. Inl (\<alpha>1 r)))) \<and>
  (S = UNIV \<longrightarrow> (\<exists> \<alpha>2\<in> qbs_Mx Y. g = (\<lambda>r. Inr (\<alpha>2 r)))) \<and>
  ((S \<noteq> {} \<and> S \<noteq> UNIV) \<longrightarrow>
     (\<exists> \<alpha>1\<in> qbs_Mx X.
      \<exists> \<alpha>2\<in> qbs_Mx Y.
          g = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))))"
    by (auto simp add: copair_qbs_Mx_def)
  consider "S = {}" | "S = UNIV" | "S \<noteq> {} \<and> S \<noteq> UNIV" by auto
  then show "g \<in> copair_qbs_Mx2 X Y"
  proof cases
    assume "S = {}"
    from hs this have "\<exists> \<alpha>1\<in> qbs_Mx X. g = (\<lambda>r. Inl (\<alpha>1 r))" by simp
    then obtain \<alpha>1 where h1:"\<alpha>1\<in> qbs_Mx X \<and> g = (\<lambda>r. Inl (\<alpha>1 r))" by auto
    have "qbs_space X \<noteq> {}"
      using qbs_empty_equiv h1
      by auto
    then have "(qbs_space X \<noteq> {} \<and> qbs_space Y = {}) \<or> (qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {})"
      by simp
    then show "g \<in> copair_qbs_Mx2 X Y"
    proof
      assume "qbs_space X \<noteq> {} \<and> qbs_space Y = {}"
      then show "g \<in> copair_qbs_Mx2 X Y" 
        by(simp add: copair_qbs_Mx2_def \<open>\<exists> \<alpha>1\<in> qbs_Mx X. g = (\<lambda>r. Inl (\<alpha>1 r))\<close>)
    next
      assume "qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}"
      then obtain \<alpha>2 where "\<alpha>2 \<in> qbs_Mx Y" using qbs_empty_equiv by force
      define S' :: "real set" 
        where "S' \<equiv> UNIV"
      define g' :: "real \<Rightarrow> 'a + 'b"
        where "g' \<equiv> (\<lambda>r::real. (if (r \<in> S') then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))"
      from \<open>qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}\<close> h1 \<open>\<alpha>2 \<in> qbs_Mx Y\<close>
      have "g' \<in> copair_qbs_Mx2 X Y" 
        by(force simp add: S'_def g'_def copair_qbs_Mx2_def)
      moreover have "g = g'"
        using h1 by(simp add: g'_def S'_def)
      ultimately show ?thesis
        by simp
    qed
  next
    assume "S = UNIV"
    from hs this have "\<exists> \<alpha>2\<in> qbs_Mx Y. g = (\<lambda>r. Inr (\<alpha>2 r))" by simp
    then obtain \<alpha>2 where h2:"\<alpha>2\<in> qbs_Mx Y \<and> g = (\<lambda>r. Inr (\<alpha>2 r))" by auto
    have "qbs_space Y \<noteq> {}"
      using qbs_empty_equiv h2
      by auto
    then have "(qbs_space X = {} \<and> qbs_space Y \<noteq> {}) \<or> (qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {})"
      by simp
    then show "g \<in> copair_qbs_Mx2 X Y"
    proof
      assume "qbs_space X = {} \<and> qbs_space Y \<noteq> {}"
      then show ?thesis
        by(simp add: copair_qbs_Mx2_def \<open>\<exists> \<alpha>2\<in> qbs_Mx Y. g = (\<lambda>r. Inr (\<alpha>2 r))\<close>)
    next
      assume "qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}"
      then obtain \<alpha>1 where "\<alpha>1 \<in> qbs_Mx X" using qbs_empty_equiv by force
      define S' :: "real set"
        where "S' \<equiv> {}"
      define g' :: "real \<Rightarrow> 'a + 'b"
        where "g' \<equiv> (\<lambda>r::real. (if (r \<in> S') then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))"
      from \<open>qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}\<close> h2 \<open>\<alpha>1 \<in> qbs_Mx X\<close>
      have "g' \<in> copair_qbs_Mx2 X Y" 
        by(force simp add: S'_def g'_def copair_qbs_Mx2_def)
      moreover have "g = g'"
        using h2 by(simp add: g'_def S'_def)
      ultimately show ?thesis
        by simp
    qed
  next
    assume "S \<noteq> {} \<and> S \<noteq> UNIV"
    then have 
    h: "\<exists> \<alpha>1\<in> qbs_Mx X.
        \<exists> \<alpha>2\<in> qbs_Mx Y.
          g = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))"
      using hs by simp
    then have "qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}"
      by (metis empty_iff qbs_empty_equiv)
    thus ?thesis
      using hs h by(auto simp add: copair_qbs_Mx2_def)
  qed

(* \<supseteq> *)
next
  fix g :: "real \<Rightarrow> 'a + 'b"
  assume "g \<in> copair_qbs_Mx2 X Y"
  then have
  h: "if qbs_space X = {} \<and> qbs_space Y = {} then False
      else if qbs_space X \<noteq> {} \<and> qbs_space Y = {} then 
                  (\<exists>\<alpha>1\<in> qbs_Mx X. g = (\<lambda>r. Inl (\<alpha>1 r)))
      else if qbs_space X = {} \<and> qbs_space Y \<noteq> {} then 
                  (\<exists>\<alpha>2\<in> qbs_Mx Y. g = (\<lambda>r. Inr (\<alpha>2 r)))
      else 
          (\<exists>S \<in> sets real_borel. \<exists>\<alpha>1\<in> qbs_Mx X. \<exists>\<alpha>2\<in> qbs_Mx Y.
           g = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r))))"
    by(simp add: copair_qbs_Mx2_def)
  consider "(qbs_space X = {} \<and> qbs_space Y = {})" |
           "(qbs_space X \<noteq> {} \<and> qbs_space Y = {})" |
           "(qbs_space X = {} \<and> qbs_space Y \<noteq> {})" |
           "(qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {})" by auto
  then show "g \<in> copair_qbs_Mx X Y"
  proof cases
    assume "qbs_space X = {} \<and> qbs_space Y = {}"
    then show ?thesis
      using \<open>g \<in> copair_qbs_Mx2 X Y\<close> by(simp add: copair_qbs_Mx2_def)
  next
    assume "qbs_space X \<noteq> {} \<and> qbs_space Y = {}"
    from h this have "\<exists>\<alpha>1\<in> qbs_Mx X. g = (\<lambda>r. Inl (\<alpha>1 r))" by simp
    thus ?thesis
      by(auto simp add: copair_qbs_Mx_def)
  next
    assume "qbs_space X = {} \<and> qbs_space Y \<noteq> {}"
    from h this have "\<exists>\<alpha>2\<in> qbs_Mx Y. g = (\<lambda>r. Inr (\<alpha>2 r))" by simp
    thus ?thesis
      unfolding copair_qbs_Mx_def 
      by(force simp add: copair_qbs_Mx_def)
  next
    assume "qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}"
    from h this have 
        "\<exists>S \<in> sets real_borel. \<exists>\<alpha>1\<in> qbs_Mx X. \<exists>\<alpha>2\<in> qbs_Mx Y.
           g = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))" by simp
    then show ?thesis
    proof(auto simp add: exE)
      fix S
      fix \<alpha>1
      fix \<alpha>2
      assume "S \<in> sets real_borel"
             "\<alpha>1 \<in> qbs_Mx X"
             "\<alpha>2 \<in> qbs_Mx Y"
             "g = (\<lambda>r. if r \<in> S then Inl (\<alpha>1 r)
                                else Inr (\<alpha>2 r))"
      consider "S = {}" | "S = UNIV" | "S \<noteq> {} \<and> S \<noteq> UNIV" by auto
      then show "(\<lambda>r. if r \<in> S then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)) \<in> copair_qbs_Mx X Y"
      proof cases
        assume "S = {}"
        then have [simp]: "(\<lambda>r. if r \<in> S then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)) = (\<lambda>r. Inr (\<alpha>2 r))"
          by simp
        have "UNIV \<in> sets real_borel" by simp
        then show ?thesis
          using \<open>\<alpha>2 \<in> qbs_Mx Y\<close> unfolding copair_qbs_Mx_def
          by(auto intro! : bexI[where x=UNIV])
      next
        assume "S = UNIV"
        then have "(\<lambda>r. if r \<in> S then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)) = (\<lambda>r. Inl (\<alpha>1 r))"
          by simp
        then show ?thesis
          using \<open>\<alpha>1 \<in> qbs_Mx X\<close> 
          by(auto simp add: copair_qbs_Mx_def)
      next
        assume "S \<noteq> {} \<and> S \<noteq> UNIV"
        then show ?thesis
          using \<open>S \<in> sets real_borel\<close> \<open>\<alpha>1 \<in> qbs_Mx X\<close> \<open>\<alpha>2 \<in> qbs_Mx Y\<close>
          by(auto simp add: copair_qbs_Mx_def)
      qed  
    qed
  qed
qed


lemma copair_qbs_f[simp]: "copair_qbs_Mx X Y \<subseteq> UNIV \<rightarrow> qbs_space X <+> qbs_space Y"
proof
  fix g
  assume "g \<in> copair_qbs_Mx X Y"
  then obtain S where hs:"S\<in> sets real_borel \<and> 
  (S = {}   \<longrightarrow> (\<exists> \<alpha>1\<in> qbs_Mx X. g = (\<lambda>r. Inl (\<alpha>1 r)))) \<and>
  (S = UNIV \<longrightarrow> (\<exists> \<alpha>2\<in> qbs_Mx Y. g = (\<lambda>r. Inr (\<alpha>2 r)))) \<and>
  ((S \<noteq> {} \<and> S \<noteq> UNIV) \<longrightarrow>
     (\<exists> \<alpha>1\<in> qbs_Mx X.
      \<exists> \<alpha>2\<in> qbs_Mx Y.
          g = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))))"
   by (auto simp add: copair_qbs_Mx_def)
  consider "S = {}" | "S = UNIV" | "S \<noteq> {} \<and> S \<noteq> UNIV" by auto
  then show "g \<in> UNIV \<rightarrow> qbs_space X <+> qbs_space Y"
  proof cases
    assume "S = {}"
    then show ?thesis
      using hs by auto
  next
    assume "S = UNIV"
    then show ?thesis
      using hs by auto
  next
    assume "S \<noteq> {} \<and> S \<noteq> UNIV"
    then have "\<exists> \<alpha>1\<in> qbs_Mx X. \<exists> \<alpha>2\<in> qbs_Mx Y.
          g = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))" using hs by simp
    then show ?thesis 
      by(auto simp add: exE)
  qed
qed

lemma copair_qbs_closed1: "qbs_closed1 (copair_qbs_Mx X Y)"
proof(auto simp add: qbs_closed1_def)
  fix g
  fix f
  assume "g \<in> copair_qbs_Mx X Y"
         "f \<in> real_borel \<rightarrow>\<^sub>M real_borel"
  then have "g \<in> copair_qbs_Mx2 X Y" using copair_qbs_Mx_equiv by auto
  consider "(qbs_space X = {} \<and> qbs_space Y = {})" |
           "(qbs_space X \<noteq> {} \<and> qbs_space Y = {})" |
           "(qbs_space X = {} \<and> qbs_space Y \<noteq> {})" |
           "(qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {})" by auto
  then have "g \<circ> f \<in> copair_qbs_Mx2 X Y"
  proof cases
    assume "qbs_space X = {} \<and> qbs_space Y = {}"
    then show ?thesis
      using \<open>g \<in> copair_qbs_Mx2 X Y\<close> qbs_empty_equiv by(simp add: copair_qbs_Mx2_def)
  next
    assume "qbs_space X \<noteq> {} \<and> qbs_space Y = {}"
    then obtain \<alpha>1 where h1:"\<alpha>1\<in> qbs_Mx X \<and> g = (\<lambda>r. Inl (\<alpha>1 r))"
      using \<open>g \<in> copair_qbs_Mx2 X Y\<close> by(auto simp add: copair_qbs_Mx2_def)
    then have "\<alpha>1 \<circ> f \<in> qbs_Mx X" 
      using \<open>f \<in> real_borel \<rightarrow>\<^sub>M real_borel\<close> by auto
    moreover have "g \<circ> f = (\<lambda>r. Inl ((\<alpha>1 \<circ> f) r))"
      using h1 by auto
    ultimately show ?thesis
      using \<open>qbs_space X \<noteq> {} \<and> qbs_space Y = {}\<close> by(force simp add: copair_qbs_Mx2_def)
  next
    assume "(qbs_space X = {} \<and> qbs_space Y \<noteq> {})"
    then obtain \<alpha>2 where h2:"\<alpha>2\<in> qbs_Mx Y \<and> g = (\<lambda>r. Inr (\<alpha>2 r))"
      using \<open>g \<in> copair_qbs_Mx2 X Y\<close> by(auto simp add: copair_qbs_Mx2_def)
    then have "\<alpha>2 \<circ> f \<in> qbs_Mx Y" 
      using \<open>f \<in> real_borel \<rightarrow>\<^sub>M real_borel\<close> by auto
    moreover have "g \<circ> f = (\<lambda>r. Inr ((\<alpha>2 \<circ> f) r))"
      using h2 by auto
    ultimately show ?thesis
      using \<open>(qbs_space X = {} \<and> qbs_space Y \<noteq> {})\<close> by(force simp add: copair_qbs_Mx2_def)
  next
    assume "qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}"
    then have "\<exists>S \<in> sets real_borel. \<exists>\<alpha>1\<in> qbs_Mx X. \<exists>\<alpha>2\<in> qbs_Mx Y.
          g = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))"
      using \<open>g \<in> copair_qbs_Mx2 X Y\<close> by(simp add: copair_qbs_Mx2_def)
    then show ?thesis
    proof(auto simp add: exE)
      fix S
      fix \<alpha>1
      fix \<alpha>2
      assume "S \<in> sets real_borel"
             "\<alpha>1\<in> qbs_Mx X"
             "\<alpha>2 \<in> qbs_Mx Y"
             "g = (\<lambda>r. if r \<in> S then Inl (\<alpha>1 r) else Inr (\<alpha>2 r))"
      have "f -` S \<in> sets real_borel"
        using \<open>f \<in> real_borel \<rightarrow>\<^sub>M real_borel\<close> \<open>S \<in> sets real_borel\<close>
        by (simp add: measurable_sets_borel)
      moreover have "\<alpha>1 \<circ> f \<in> qbs_Mx X"
        using \<open>\<alpha>1\<in> qbs_Mx X\<close> \<open>f \<in> real_borel \<rightarrow>\<^sub>M real_borel\<close> qbs_decomp
        by(auto simp add: qbs_closed1_def)
      moreover have "\<alpha>2 \<circ> f \<in> qbs_Mx Y"
        using \<open>\<alpha>2\<in> qbs_Mx Y\<close> \<open>f \<in> real_borel \<rightarrow>\<^sub>M real_borel\<close> qbs_decomp
        by(auto simp add: qbs_closed1_def)
      moreover have 
        "(\<lambda>r. if r \<in> S then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)) \<circ> f = (\<lambda>r. if r \<in> f -` S then Inl ((\<alpha>1 \<circ> f) r) else Inr ((\<alpha>2 \<circ> f) r))"
        by auto
      ultimately show "(\<lambda>r. if r \<in> S then Inl (\<alpha>1 r)  else Inr (\<alpha>2 r)) \<circ> f \<in> copair_qbs_Mx2 X Y"
        using \<open>qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}\<close> by(force simp add: copair_qbs_Mx2_def)
    qed
  qed
  thus "g \<circ> f \<in> copair_qbs_Mx X Y"
    using copair_qbs_Mx_equiv by auto
qed

lemma copair_qbs_closed2: "qbs_closed2 (qbs_space X <+> qbs_space Y) (copair_qbs_Mx X Y)"
proof(auto simp add: qbs_closed2_def)
  fix x
  assume "x \<in> qbs_space X"
  define \<alpha>1 :: "real \<Rightarrow> _" where "\<alpha>1 \<equiv> (\<lambda>r. x)"
  have "\<alpha>1 \<in> qbs_Mx X" using \<open>x \<in> qbs_space X\<close> qbs_decomp 
    by(force simp add: qbs_closed2_def \<alpha>1_def )
  moreover have "(\<lambda>r. Inl x) = (\<lambda>l. Inl (\<alpha>1 l))" by (simp add: \<alpha>1_def)
  moreover have "{} \<in> sets real_borel" by auto
  ultimately show "(\<lambda>r. Inl x) \<in> copair_qbs_Mx X Y"
    by(auto simp add: copair_qbs_Mx_def)
next
  fix y
  assume "y \<in> qbs_space Y"
  define \<alpha>2 :: "real \<Rightarrow> _" where "\<alpha>2 \<equiv> (\<lambda>r. y)"
  have "\<alpha>2 \<in> qbs_Mx Y" using \<open>y \<in> qbs_space Y\<close> qbs_decomp 
    by(force simp add: qbs_closed2_def \<alpha>2_def )
  moreover have "(\<lambda>r. Inr y) = (\<lambda>l. Inr (\<alpha>2 l))" by (simp add: \<alpha>2_def)
  moreover have "UNIV \<in> sets real_borel" by auto
  ultimately show "(\<lambda>r. Inr y) \<in> copair_qbs_Mx X Y"
    unfolding copair_qbs_Mx_def
    by(auto intro!: bexI[where x=UNIV])
qed

lemma copair_qbs_closed3: "qbs_closed3 (copair_qbs_Mx X Y)"
proof(auto simp add: qbs_closed3_def)
  fix P :: "real \<Rightarrow> nat"
  fix Fi :: "nat \<Rightarrow> real \<Rightarrow>_ + _"
  assume "\<forall>i. P -` {i} \<in> sets real_borel"
         "\<forall>i. Fi i \<in> copair_qbs_Mx X Y"
  then have "\<forall>i. Fi i \<in> copair_qbs_Mx2 X Y" using copair_qbs_Mx_equiv by blast
  consider "(qbs_space X = {} \<and> qbs_space Y = {})" |
           "(qbs_space X \<noteq> {} \<and> qbs_space Y = {})" |
           "(qbs_space X = {} \<and> qbs_space Y \<noteq> {})" |
           "(qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {})" by auto
  then have "(\<lambda>r. Fi (P r) r) \<in> copair_qbs_Mx2 X Y"
  proof cases
    assume "qbs_space X = {} \<and> qbs_space Y = {}"
    then show ?thesis
      using \<open>\<forall>i. Fi i \<in> copair_qbs_Mx2 X Y\<close> qbs_empty_equiv 
      by(simp add: copair_qbs_Mx2_def)
  next
    assume "qbs_space X \<noteq> {} \<and> qbs_space Y = {}"
    then have "\<forall>i. \<exists>\<alpha>i. \<alpha>i \<in> qbs_Mx X \<and> Fi i = (\<lambda>r. Inl (\<alpha>i r))"
      using \<open>\<forall>i. Fi i \<in> copair_qbs_Mx2 X Y\<close> by(auto simp add: copair_qbs_Mx2_def)
    then have "\<exists>\<alpha>1. \<forall>i. \<alpha>1 i \<in> qbs_Mx X \<and> Fi i = (\<lambda>r. Inl (\<alpha>1 i r))"
      by(rule choice)
    then obtain \<alpha>1 :: "nat \<Rightarrow> real \<Rightarrow> _" 
      where h1: "\<forall>i. \<alpha>1 i \<in> qbs_Mx X \<and> Fi i = (\<lambda>r. Inl (\<alpha>1 i r))" by auto
    define \<beta> :: "real \<Rightarrow> _" 
      where "\<beta> \<equiv> (\<lambda>r. \<alpha>1 (P r) r)"
    from \<open>\<forall>i. P -` {i} \<in> sets real_borel\<close> h1
    have "\<beta> \<in> qbs_Mx X"
      by (simp add: \<beta>_def)
    moreover have "(\<lambda>r. Fi (P r) r) = (\<lambda>r. Inl (\<beta> r))"
      using h1 by(simp add: \<beta>_def)
    ultimately show ?thesis
      using \<open>qbs_space X \<noteq> {} \<and> qbs_space Y = {}\<close> by (auto simp add: copair_qbs_Mx2_def)
  next
    assume "qbs_space X = {} \<and> qbs_space Y \<noteq> {}"
    then have "\<forall>i. \<exists>\<alpha>i. \<alpha>i \<in> qbs_Mx Y \<and> Fi i = (\<lambda>r. Inr (\<alpha>i r))"
      using \<open>\<forall>i. Fi i \<in> copair_qbs_Mx2 X Y\<close> by(auto simp add: copair_qbs_Mx2_def)
    then have "\<exists>\<alpha>2. \<forall>i. \<alpha>2 i \<in> qbs_Mx Y \<and> Fi i = (\<lambda>r. Inr (\<alpha>2 i r))"
      by(rule choice)
    then obtain \<alpha>2 :: "nat \<Rightarrow> real \<Rightarrow> _" 
      where h2: "\<forall>i. \<alpha>2 i \<in> qbs_Mx Y \<and> Fi i = (\<lambda>r. Inr (\<alpha>2 i r))" by auto
    define \<beta> :: "real \<Rightarrow> _" 
      where "\<beta> \<equiv> (\<lambda>r. \<alpha>2 (P r) r)"
    from \<open>\<forall>i. P -` {i} \<in> sets real_borel\<close> h2 qbs_decomp
    have "\<beta> \<in> qbs_Mx Y"
      by(simp add: \<beta>_def)
    moreover have "(\<lambda>r. Fi (P r) r) = (\<lambda>r. Inr (\<beta> r))"
      using h2 by(simp add: \<beta>_def)
    ultimately show ?thesis
      using \<open>qbs_space X = {} \<and> qbs_space Y \<noteq> {}\<close> by (auto simp add: copair_qbs_Mx2_def)
  next
    assume "qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}"
    then have "\<forall>i. \<exists>Si. Si \<in> sets real_borel \<and> (\<exists>\<alpha>1i\<in> qbs_Mx X. \<exists>\<alpha>2i\<in> qbs_Mx Y.
                   Fi i = (\<lambda>r::real. (if (r \<in> Si) then Inl (\<alpha>1i r) else Inr (\<alpha>2i r))))"
      using \<open>\<forall>i. Fi i \<in> copair_qbs_Mx2 X Y\<close> by (auto simp add: copair_qbs_Mx2_def)
    then have "\<exists>S. \<forall>i. S i \<in> sets real_borel \<and> (\<exists>\<alpha>1i\<in> qbs_Mx X. \<exists>\<alpha>2i\<in> qbs_Mx Y.
                   Fi i = (\<lambda>r::real. (if (r \<in> S i) then Inl (\<alpha>1i r) else Inr (\<alpha>2i r))))"
      by(rule choice)
    then obtain S :: "nat \<Rightarrow> real set" 
      where hs :"\<forall>i. S i \<in> sets real_borel \<and> (\<exists>\<alpha>1i\<in> qbs_Mx X. \<exists>\<alpha>2i\<in> qbs_Mx Y.
                   Fi i = (\<lambda>r::real. (if (r \<in> S i) then Inl (\<alpha>1i r) else Inr (\<alpha>2i r))))"
      by auto
    then have "\<forall>i. \<exists>\<alpha>1i. \<alpha>1i \<in> qbs_Mx X \<and> (\<exists>\<alpha>2i\<in> qbs_Mx Y.
               Fi i = (\<lambda>r::real. (if (r \<in> S i) then Inl (\<alpha>1i r) else Inr (\<alpha>2i r))))"
      by blast
    then have "\<exists>\<alpha>1. \<forall>i. \<alpha>1 i \<in> qbs_Mx X \<and> (\<exists>\<alpha>2i\<in> qbs_Mx Y.
               Fi i = (\<lambda>r::real. (if (r \<in> S i) then Inl (\<alpha>1 i r) else Inr (\<alpha>2i r))))"
      by(rule choice)
    then obtain \<alpha>1 
      where h1: "\<forall>i. \<alpha>1 i \<in> qbs_Mx X \<and> (\<exists>\<alpha>2i\<in> qbs_Mx Y.
               Fi i = (\<lambda>r::real. (if (r \<in> S i) then Inl (\<alpha>1 i r) else Inr (\<alpha>2i r))))"
      by auto
    define \<beta>1 :: "real \<Rightarrow> _" 
      where "\<beta>1 \<equiv> (\<lambda>r. \<alpha>1 (P r) r)"
    from \<open>\<forall>i. P -` {i} \<in> sets real_borel\<close> h1 qbs_decomp
    have "\<beta>1 \<in> qbs_Mx X"
      by(simp add: \<beta>1_def)
    from h1 have "\<forall>i. \<exists>\<alpha>2i. \<alpha>2i\<in> qbs_Mx Y \<and>
               Fi i = (\<lambda>r::real. (if (r \<in> S i) then Inl (\<alpha>1 i r) else Inr (\<alpha>2i r)))"
      by auto
    then have "\<exists>\<alpha>2. \<forall>i. \<alpha>2 i\<in> qbs_Mx Y \<and>
               Fi i = (\<lambda>r::real. (if (r \<in> S i) then Inl (\<alpha>1 i r) else Inr (\<alpha>2 i r)))"
      by(rule choice)
    then obtain \<alpha>2 
      where h2: "\<forall>i. \<alpha>2 i\<in> qbs_Mx Y \<and>
               Fi i = (\<lambda>r::real. (if (r \<in> S i) then Inl (\<alpha>1 i r) else Inr (\<alpha>2 i r)))"
      by auto
    define \<beta>2 :: "real \<Rightarrow> _" 
      where "\<beta>2 \<equiv> (\<lambda>r. \<alpha>2 (P r) r)"
    from \<open>\<forall>i. P -` {i} \<in> sets real_borel\<close> h2 qbs_decomp
    have "\<beta>2 \<in> qbs_Mx Y"
      by(simp add: \<beta>2_def)
    define A :: "nat \<Rightarrow> real set"
      where "A \<equiv> (\<lambda>i. S i \<inter> P -` {i})"
    have "\<forall>i. A i \<in> sets real_borel"
      using A_def \<open>\<forall>i. P -` {i} \<in> sets real_borel\<close> hs by blast
    define S' :: "real set"
      where "S' \<equiv> {r. r \<in> S (P r)}"
    have "S' = (\<Union>i::nat. A i)"
      by(auto simp add: S'_def A_def)
    hence "S' \<in> sets real_borel"
      using \<open>\<forall>i. A i \<in> sets real_borel\<close> by auto
    from h2 have "(\<lambda>r. Fi (P r) r) = (\<lambda>r. (if r \<in> S' then Inl (\<beta>1  r)
                                                      else Inr (\<beta>2 r)))"
      by(auto simp add: \<beta>1_def \<beta>2_def S'_def)
    thus "(\<lambda>r. Fi (P r) r) \<in> copair_qbs_Mx2 X Y"
      using \<open>qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}\<close> \<open>S' \<in> sets real_borel\<close> \<open>\<beta>1 \<in> qbs_Mx X\<close> \<open>\<beta>2 \<in> qbs_Mx Y\<close>
      by(auto simp add: copair_qbs_Mx2_def)
  qed
  thus "(\<lambda>r. Fi (P r) r) \<in> copair_qbs_Mx X Y"
    using copair_qbs_Mx_equiv by auto
qed

lemma copair_qbs_correct: "Rep_quasi_borel (copair_qbs X Y) = (qbs_space X <+> qbs_space Y, copair_qbs_Mx X Y)"
  unfolding copair_qbs_def
  by(auto intro!: Abs_quasi_borel_inverse copair_qbs_f simp: copair_qbs_closed2 copair_qbs_closed1 copair_qbs_closed3)

lemma copair_qbs_space[simp]: "qbs_space (copair_qbs X Y) = qbs_space X <+> qbs_space Y"
  by(simp add: qbs_space_def copair_qbs_correct)

lemma copair_qbs_Mx[simp]: "qbs_Mx (copair_qbs X Y) = copair_qbs_Mx X Y"
  by(simp add: qbs_Mx_def copair_qbs_correct)


lemma Inl_qbs_morphism:
  "Inl \<in> X \<rightarrow>\<^sub>Q X <+>\<^sub>Q Y"
proof(rule qbs_morphismI)
  fix \<alpha>
  assume "\<alpha> \<in> qbs_Mx X"
  moreover have "Inl \<circ> \<alpha> = (\<lambda>r. Inl (\<alpha> r))" by auto
  ultimately show "Inl \<circ> \<alpha> \<in> qbs_Mx (X <+>\<^sub>Q Y)"
    by(auto simp add: copair_qbs_Mx_def)
qed

lemma Inr_qbs_morphism:
  "Inr \<in> Y \<rightarrow>\<^sub>Q X <+>\<^sub>Q Y"
proof(rule qbs_morphismI)
  fix \<alpha>
  assume "\<alpha> \<in> qbs_Mx Y"
  moreover have "Inr \<circ> \<alpha> = (\<lambda>r. Inr (\<alpha> r))" by auto
  ultimately show "Inr \<circ> \<alpha> \<in> qbs_Mx (X <+>\<^sub>Q Y)"
    by(auto intro!: bexI[where x=UNIV] simp add: copair_qbs_Mx_def)
qed

lemma case_sum_preserves_morphisms:
  assumes "f \<in> X \<rightarrow>\<^sub>Q Z"
      and "g \<in> Y \<rightarrow>\<^sub>Q Z"
    shows "case_sum f g \<in> X <+>\<^sub>Q Y \<rightarrow>\<^sub>Q Z"
proof(rule qbs_morphismI;auto)
  fix \<alpha>
  assume "\<alpha> \<in> copair_qbs_Mx X Y"
  then obtain S where hs:"S\<in> sets real_borel \<and> 
  (S = {}   \<longrightarrow> (\<exists> \<alpha>1\<in> qbs_Mx X. \<alpha> = (\<lambda>r. Inl (\<alpha>1 r)))) \<and>
  (S = UNIV \<longrightarrow> (\<exists> \<alpha>2\<in> qbs_Mx Y. \<alpha> = (\<lambda>r. Inr (\<alpha>2 r)))) \<and>
  ((S \<noteq> {} \<and> S \<noteq> UNIV) \<longrightarrow>
     (\<exists> \<alpha>1\<in> qbs_Mx X.
      \<exists> \<alpha>2\<in> qbs_Mx Y.
          \<alpha> = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))))"
    by (auto simp add: copair_qbs_Mx_def)
  consider "S = {}" | "S = UNIV" | "S \<noteq> {} \<and> S \<noteq> UNIV" by auto
  then show "case_sum f g \<circ> \<alpha> \<in> qbs_Mx Z"
  proof cases
    assume "S = {}"
    then obtain \<alpha>1 where h1: "\<alpha>1\<in> qbs_Mx X \<and> \<alpha> = (\<lambda>r. Inl (\<alpha>1 r))"
      using hs by auto
    then have "f \<circ> \<alpha>1 \<in> qbs_Mx Z"
      using assms by(auto simp add: qbs_morphism_def)
    moreover have "case_sum f g \<circ> \<alpha> = f \<circ> \<alpha>1"
      using h1 by auto
    ultimately show ?thesis by simp
  next
    assume "S = UNIV"
    then obtain \<alpha>2 where h2: "\<alpha>2\<in> qbs_Mx Y \<and> \<alpha> = (\<lambda>r. Inr (\<alpha>2 r))"
      using hs by auto
    then have "g \<circ> \<alpha>2 \<in> qbs_Mx Z"
      using assms by(auto simp add: qbs_morphism_def)
    moreover have "case_sum f g \<circ> \<alpha> = g \<circ> \<alpha>2"
      using h2 by auto
    ultimately show ?thesis by simp
  next
    assume "S \<noteq> {} \<and> S \<noteq> UNIV"
    then obtain \<alpha>1 \<alpha>2 where h: "\<alpha>1\<in> qbs_Mx X \<and> \<alpha>2\<in> qbs_Mx Y \<and>
         \<alpha> = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))"
      using hs by auto
    define F :: "nat \<Rightarrow> real \<Rightarrow> _"
      where "F \<equiv> (\<lambda>i r. (if i = 0 then (f \<circ> \<alpha>1) r
                                    else (g \<circ> \<alpha>2) r))"
    define P :: "real \<Rightarrow> nat"
      where "P \<equiv> (\<lambda>r. if r \<in> S then 0 else 1)"
    have "f \<circ> \<alpha>1 \<in> qbs_Mx Z"
      using assms h by(simp add: qbs_morphism_def)
    have "g \<circ> \<alpha>2 \<in> qbs_Mx Z"
      using assms h by(simp add: qbs_morphism_def)
    have "\<forall>i. F i \<in> qbs_Mx Z"
    proof(auto simp add: F_def)
      fix i :: nat
      consider "i = 0" | "i \<noteq> 0" by auto
      then show "(\<lambda>r. if i = 0 then (f \<circ> \<alpha>1) r else (g \<circ> \<alpha>2) r) \<in> qbs_Mx Z"
      proof cases
        assume "i = 0"
        then have "(\<lambda>r. if i = 0 then (f \<circ> \<alpha>1) r else (g \<circ> \<alpha>2) r) = f \<circ> \<alpha>1" by auto
        then show ?thesis
          using \<open>f \<circ> \<alpha>1 \<in> qbs_Mx Z\<close> by simp
      next
        assume "i \<noteq> 0"
        then have "(\<lambda>r. if i = 0 then (f \<circ> \<alpha>1) r else (g \<circ> \<alpha>2) r) = g \<circ> \<alpha>2" by auto
        then show ?thesis
          using \<open>g \<circ> \<alpha>2 \<in> qbs_Mx Z\<close> by simp
      qed
    qed
    moreover have "\<forall>i. P -`{i} \<in> sets real_borel"
    proof
      fix i :: nat
      consider "i = 0" | "i = 1" | "i \<noteq> 0 \<and> i \<noteq> 1" by auto
      then show "P -`{i} \<in> sets real_borel"
      proof cases
        assume "i = 0"
        then show ?thesis
          using hs by(simp add: P_def)
      next
        assume "i = 1"
        then show ?thesis
          using hs by (simp add: P_def borel_comp)
      next
        assume "i \<noteq> 0 \<and> i \<noteq> 1"
        then show ?thesis by(simp add: P_def)
      qed
    qed
    ultimately have "(\<lambda>r. F (P r) r) \<in> qbs_Mx Z"
      by simp
    moreover have "case_sum f g \<circ> \<alpha> = (\<lambda>r. F (P r) r)"
      using h by(auto simp add: F_def P_def)
    ultimately show "case_sum f g \<circ> \<alpha> \<in> qbs_Mx Z" by simp
  qed
qed


lemma map_sum_preserves_morphisms:
  assumes "f \<in> X  \<rightarrow>\<^sub>Q Y"
      and "g \<in> X' \<rightarrow>\<^sub>Q Y'"
    shows "map_sum f g \<in> X <+>\<^sub>Q X' \<rightarrow>\<^sub>Q Y <+>\<^sub>Q Y'"
proof(rule qbs_morphismI,simp)
  fix \<alpha>
  assume "\<alpha> \<in> copair_qbs_Mx X X'"
  then obtain S where hs:"S\<in> sets real_borel \<and> 
  (S = {}   \<longrightarrow> (\<exists> \<alpha>1\<in> qbs_Mx X. \<alpha> = (\<lambda>r. Inl (\<alpha>1 r)))) \<and>
  (S = UNIV \<longrightarrow> (\<exists> \<alpha>2\<in> qbs_Mx X'. \<alpha> = (\<lambda>r. Inr (\<alpha>2 r)))) \<and>
  ((S \<noteq> {} \<and> S \<noteq> UNIV) \<longrightarrow>
     (\<exists> \<alpha>1\<in> qbs_Mx X.
      \<exists> \<alpha>2\<in> qbs_Mx X'.
          \<alpha> = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))))"
    by (auto simp add: copair_qbs_Mx_def)
  consider "S = {}" | "S = UNIV" | "S \<noteq> {} \<and> S \<noteq> UNIV" by auto
  then show "map_sum f g \<circ> \<alpha> \<in> copair_qbs_Mx Y Y'"
  proof cases
    assume "S = {}"
    then obtain \<alpha>1 where h1: "\<alpha>1\<in> qbs_Mx X \<and> \<alpha> = (\<lambda>r. Inl (\<alpha>1 r))"
      using hs by auto
    define f' :: "real \<Rightarrow> _" where "f' \<equiv> f \<circ> \<alpha>1"
    then have "f' \<in> qbs_Mx Y"
      using assms h1 by(simp add: qbs_morphism_def)
    moreover have "map_sum f g \<circ> \<alpha> = (\<lambda>r. Inl (f' r))"
      using h1 by (auto simp add: f'_def)
    moreover have "{} \<in> sets real_borel" by simp
    ultimately show ?thesis
      by(auto simp add: copair_qbs_Mx_def)
  next
    assume "S = UNIV"
    then obtain \<alpha>2 where h2: "\<alpha>2\<in> qbs_Mx X' \<and> \<alpha> = (\<lambda>r. Inr (\<alpha>2 r))"
      using hs by auto
    define g' :: "real \<Rightarrow> _" where "g' \<equiv> g \<circ> \<alpha>2"
    then have "g' \<in> qbs_Mx Y'"
      using assms h2 by(simp add: qbs_morphism_def)
    moreover have "map_sum f g \<circ> \<alpha> = (\<lambda>r. Inr (g' r))"
      using h2 by (auto simp add: g'_def)
    ultimately show ?thesis
      by(auto intro!: bexI[where x=UNIV] simp add: copair_qbs_Mx_def)
  next
    assume "S \<noteq> {} \<and> S \<noteq> UNIV"
    then obtain \<alpha>1 \<alpha>2 where h: "\<alpha>1\<in> qbs_Mx X \<and> \<alpha>2\<in> qbs_Mx X' \<and>
         \<alpha> = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))"
      using hs by auto
    define f' :: "real \<Rightarrow> _" where "f' \<equiv> f \<circ> \<alpha>1"
    define g' :: "real \<Rightarrow> _" where "g' \<equiv> g \<circ> \<alpha>2"
    have "f' \<in> qbs_Mx Y"
      using assms h by(auto simp: f'_def)
    moreover have "g' \<in> qbs_Mx Y'"
      using assms h by(auto simp: g'_def)
    moreover have "map_sum f g \<circ> \<alpha> = (\<lambda>r::real. (if (r \<in> S) then Inl (f' r) else Inr (g' r)))"
      using h by(auto simp add: f'_def g'_def)
    moreover have "S \<in> sets real_borel" using hs by simp
    ultimately show ?thesis
      using \<open>S \<noteq> {} \<and> S \<noteq> UNIV\<close> by(auto simp add: copair_qbs_Mx_def)
  qed
qed


end