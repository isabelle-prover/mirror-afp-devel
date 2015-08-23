(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Missing Ring\<close>

text \<open>This theory contains several lemmas which might be of interest to the Isabelle distribution.\<close>

theory Missing_Ring
imports
  "~~/src/HOL/Algebra/Ring"
begin

context comm_monoid
begin

lemma finprod_reindex_bij_betw: "bij_betw h S T 
  \<Longrightarrow> g \<in> h ` S \<rightarrow> carrier G 
  \<Longrightarrow> finprod G (\<lambda>x. g (h x)) S = finprod G g T"
  using finprod_reindex[of g h S] unfolding bij_betw_def by auto

lemma finprod_reindex_bij_witness:
  assumes witness:
    "\<And>a. a \<in> S \<Longrightarrow> i (j a) = a"
    "\<And>a. a \<in> S \<Longrightarrow> j a \<in> T"
    "\<And>b. b \<in> T \<Longrightarrow> j (i b) = b"
    "\<And>b. b \<in> T \<Longrightarrow> i b \<in> S"
  assumes eq:
    "\<And>a. a \<in> S \<Longrightarrow> h (j a) = g a"
  assumes g: "g \<in> S \<rightarrow> carrier G"
  and h: "h \<in> j ` S \<rightarrow> carrier G"
  shows "finprod G g S = finprod G h T"
proof -
  have b: "bij_betw j S T"
    using bij_betw_byWitness[where A=S and f=j and f'=i and A'=T] witness by auto
  have fp: "finprod G g S = finprod G (\<lambda>x. h (j x)) S"
    by (rule finprod_cong, insert eq g, auto)
  show ?thesis
    using finprod_reindex_bij_betw[OF b h] unfolding fp .
qed
end

lemmas (in abelian_monoid) finsum_reindex_bij_witness = add.finprod_reindex_bij_witness

locale csemiring = semiring + comm_monoid R

context cring
begin
sublocale csemiring ..
end

lemma (in comm_monoid) finprod_one': 
  "(\<And> a. a \<in> A \<Longrightarrow> f a = \<one>) \<Longrightarrow> finprod G f A = \<one>"
  by (induct A rule: infinite_finite_induct, auto)

lemma (in comm_monoid) finprod_split: 
  "finite A \<Longrightarrow> f ` A \<subseteq> carrier G \<Longrightarrow> a \<in> A \<Longrightarrow> finprod G f A = f a \<otimes> finprod G f (A - {a})"
  by (rule trans[OF trans[OF _ finprod_Un_disjoint[of "{a}" "A - {a}" f]]], auto,
  rule arg_cong[of _ _ "finprod G f"], auto)

lemma (in comm_monoid) finprod_finprod:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> (\<And> a b. a \<in> A  \<Longrightarrow> b \<in> B \<Longrightarrow> g a b \<in> carrier G) \<Longrightarrow>
  finprod G (\<lambda> a. finprod G (g a) B) A = finprod G (\<lambda> (a,b). g a b) (A \<times> B)"
proof (induct A rule: finite_induct)
  case (insert a' A)
  note IH = this
  let ?l = "(\<Otimes>a\<in>insert a' A. finprod G (g a) B)"
  let ?r = "(\<Otimes>a\<in>insert a' A \<times> B. case a of (a, b) \<Rightarrow> g a b)"
  have "?l = finprod G (g a') B \<otimes> (\<Otimes>a\<in>A. finprod G (g a) B)"
    using IH by simp
  also have "(\<Otimes>a\<in>A. finprod G (g a) B) = finprod G (\<lambda> (a,b). g a b) (A \<times> B)"
    by (rule IH(3), insert IH, auto)
  finally have idl: "?l = finprod G (g a') B \<otimes> finprod G (\<lambda> (a,b). g a b) (A \<times> B)" .
  from IH(2) have "insert a' A \<times> B = {a'} \<times> B \<union> A \<times> B" by auto
  hence "?r = (\<Otimes>a\<in>{a'} \<times> B \<union> A \<times> B. case a of (a, b) \<Rightarrow> g a b)" by simp
  also have "\<dots> = (\<Otimes>a\<in>{a'} \<times> B. case a of (a, b) \<Rightarrow> g a b) \<otimes> (\<Otimes>a\<in> A \<times> B. case a of (a, b) \<Rightarrow> g a b)"
    by (rule finprod_Un_disjoint, insert IH, auto)
  also have "(\<Otimes>a\<in>{a'} \<times> B. case a of (a, b) \<Rightarrow> g a b) = finprod G (g a') B"
    using IH(4) IH(5)
  proof (induct B rule: finite_induct)
    case (insert b' B)
    note IH = this
    have id: "(\<Otimes>a\<in>{a'} \<times> B. case a of (a, b) \<Rightarrow> g a b) = finprod G (g a') B"
      by (rule IH(3)[OF IH(4)], auto)
    have id2: "\<And> x F. {a'} \<times> insert x F = insert (a',x) ({a'} \<times> F)" by auto
    have id3: "(\<Otimes>a\<in>insert (a', b') ({a'} \<times> B). case a of (a, b) \<Rightarrow> g a b)
      = g a' b' \<otimes> (\<Otimes>a\<in>({a'} \<times> B). case a of (a, b) \<Rightarrow> g a b)"
      by (rule trans[OF finprod_insert], insert IH, auto)
    show ?case unfolding id2 id3 id
      by (rule sym, rule finprod_insert, insert IH, auto)
  qed simp
  finally have idr: "?r = finprod G (g a') B \<otimes> (\<Otimes>a\<in>A \<times> B. case a of (a, b) \<Rightarrow> g a b)" .
  show ?case unfolding idl idr ..
qed simp

lemma (in comm_monoid) finprod_swap:
  assumes "finite A" "finite B" "\<And> a b. a \<in> A  \<Longrightarrow> b \<in> B \<Longrightarrow> g a b \<in> carrier G"
  shows "finprod G (\<lambda> (b,a). g a b) (B \<times> A) = finprod G (\<lambda> (a,b). g a b) (A \<times> B)"
proof -
  have [simp]: "(\<lambda>(a, b). (b, a)) ` (A \<times> B) = B \<times> A" by auto
  have [simp]: "(\<lambda> x. case case x of (a, b) \<Rightarrow> (b, a) of (a, b) \<Rightarrow> g b a) = (\<lambda> (a,b). g a b)"
    by (intro ext, auto)
  show ?thesis 
    by (rule trans[OF trans[OF _ finprod_reindex[of "\<lambda> (a,b). g b a" "\<lambda> (a,b). (b,a)"]]],
    insert assms, auto simp: inj_on_def)
qed

lemma (in comm_monoid) finprod_finprod_swap:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> (\<And> a b. a \<in> A  \<Longrightarrow> b \<in> B \<Longrightarrow> g a b \<in> carrier G) \<Longrightarrow>
  finprod G (\<lambda> a. finprod G (g a) B) A = finprod G (\<lambda> b. finprod G (\<lambda> a. g a b) A) B"
  using finprod_finprod[of A B] finprod_finprod[of B A] finprod_swap[of A B]
  by simp



lemmas (in semiring) finsum_zero' = add.finprod_one' 
lemmas (in semiring) finsum_split = add.finprod_split 
lemmas (in semiring) finsum_finsum_swap = add.finprod_finprod_swap


lemma (in csemiring) finprod_zero: 
  "finite A \<Longrightarrow> f \<in> A \<rightarrow> carrier R \<Longrightarrow> \<exists>a\<in>A. f a = \<zero>
   \<Longrightarrow> finprod R f A = \<zero>"
proof (induct A rule: finite_induct)
  case (insert a A)
  from finprod_insert[OF insert(1-2), of f] insert(4)
  have ins: "finprod R f (insert a A) = f a \<otimes> finprod R f A" by simp
  have fA: "finprod R f A \<in> carrier R"
    by (rule finprod_closed, insert insert, auto)
  show ?case
  proof (cases "f a = \<zero>")
    case True
    with fA show ?thesis unfolding ins by simp
  next
    case False
    with insert(5) have "\<exists> a \<in> A. f a = \<zero>" by auto
    from insert(3)[OF _ this] insert have "finprod R f A = \<zero>" by auto
    with insert show ?thesis unfolding ins by auto
  qed
qed simp

lemma (in semiring) finsum_product:
  assumes A: "finite A" and B: "finite B"
  and f: "f \<in> A \<rightarrow> carrier R" and g: "g \<in> B \<rightarrow> carrier R" 
  shows "finsum R f A \<otimes> finsum R g B = (\<Oplus>i\<in>A. \<Oplus>j\<in>B. f i \<otimes> g j)"
  unfolding finsum_ldistr[OF A finsum_closed[OF g] f]
proof (rule finsum_cong'[OF refl])
  fix a
  assume a: "a \<in> A"
  show "f a \<otimes> finsum R g B = (\<Oplus>j\<in>B. f a \<otimes> g j)"
  by (rule finsum_rdistr[OF B _ g], insert a f, auto)
qed (insert f g B, auto intro: finsum_closed)
    
lemma (in semiring) Units_one_side_I: 
  "a \<in> carrier R \<Longrightarrow> p \<in> Units R \<Longrightarrow> p \<otimes> a = \<one> \<Longrightarrow> a \<in> Units R"
  "a \<in> carrier R \<Longrightarrow> p \<in> Units R \<Longrightarrow> a \<otimes> p = \<one> \<Longrightarrow> a \<in> Units R"
  by (metis Units_closed Units_inv_Units Units_l_inv inv_unique)+

end