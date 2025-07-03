(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Missing Ring\<close>

text \<open>This theory contains several lemmas which might be of interest to the Isabelle distribution.\<close>

theory Missing_Ring
  imports
  "Missing_Misc"
  "HOL-Algebra.Ring"
begin

class ordered_idom = idom + ordered_semiring_strict +
  assumes zero_less_one [simp]: "0 < 1" begin

subclass ordered_ring ..
subclass ordered_comm_semiring 
  by(unfold_locales, fact mult_left_mono)
subclass ordered_semiring_1
  by unfold_locales auto

lemma of_nat_ge_0[simp]: "of_nat x \<ge> 0"
proof (induct x)
  case 0 thus ?case by auto
  next case (Suc x)
    hence "0 \<le> of_nat x" by auto
    also have "of_nat x < of_nat (Suc x)" by auto
    finally show ?case by auto
qed

lemma of_nat_eq_0[simp]: "of_nat x = 0 \<longleftrightarrow> x = 0"
proof(induct x,simp)
  case (Suc x)
    have "of_nat (Suc x) > 0" apply(rule le_less_trans[of _ "of_nat x"]) by auto
    thus ?case by auto
qed

lemma inj_of_nat: "inj (of_nat :: nat \<Rightarrow> 'a)"
proof(rule injI)
  fix x y show "of_nat x = of_nat y \<Longrightarrow> x = y"
  proof (induct x arbitrary: y)
    case 0 thus ?case
      proof (induct y)
        case 0 thus ?case by auto
        next case (Suc y)
          hence "of_nat (Suc y) = 0" by auto
          hence "Suc y = 0" unfolding of_nat_eq_0 by auto
          hence False by auto
          thus ?case by auto
      qed
    next case (Suc x)
      thus ?case
      proof (induct y)
        case 0
          hence "of_nat (Suc x) = 0" by auto
          hence "Suc x = 0" unfolding of_nat_eq_0 by auto
          hence False by auto
          thus ?case by auto
        next case (Suc y) thus ?case by auto
      qed
  qed
qed

subclass ring_char_0 by(unfold_locales, fact inj_of_nat)

end

(*
instance linordered_idom \<subseteq> ordered_semiring_strict by (intro_classes,auto)
instance linordered_idom \<subseteq> ordered_idom by (intro_classes, auto)
*)

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



lemmas (in semiring) finsum_zero' = add.finprod_one_eqI 
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


lemma permutes_funcset: "p permutes A \<Longrightarrow> (p ` A \<rightarrow> B) = (A \<rightarrow> B)"
  by (simp add: permutes_image)

context comm_monoid
begin
lemma finprod_permute:
  assumes p: "p permutes S"
  and f: "f \<in> S \<rightarrow> carrier G"
  shows "finprod G f S = finprod G (f \<circ> p) S"
proof -
  from \<open>p permutes S\<close> have "inj p"
    by (rule permutes_inj)
  then have "inj_on p S"
    by (auto intro: inj_on_subset)
  from finprod_reindex[OF _ this, unfolded permutes_image[OF p], OF f]
  show ?thesis unfolding o_def .
qed

lemma finprod_singleton_set[simp]: assumes "f a \<in> carrier G"
  shows "finprod G f {a} = f a"
proof -
  have "finprod G f {a} = f a \<otimes> finprod G f {}"
    by (rule finprod_insert, insert assms, auto)
  also have "\<dots> = f a" using assms by auto
  finally show ?thesis .
qed
end

lemmas (in semiring) finsum_permute = add.finprod_permute
lemmas (in semiring) finsum_singleton_set = add.finprod_singleton_set

context cring
begin

lemma finsum_permutations_inverse: 
  assumes f: "f \<in> {p. p permutes S} \<rightarrow> carrier R"
  shows "finsum R f {p. p permutes S} = finsum R (\<lambda>p. f(Hilbert_Choice.inv p)) {p. p permutes S}"
  (is "?lhs = ?rhs")
proof -
  let ?inv = "Hilbert_Choice.inv"
  let ?S = "{p . p permutes S}"
  have th0: "inj_on ?inv ?S"
  proof (auto simp add: inj_on_def)
    fix q r
    assume q: "q permutes S"
      and r: "r permutes S"
      and qr: "?inv q = ?inv r"
    then have "?inv (?inv q) = ?inv (?inv r)"
      by simp
    with permutes_inv_inv[OF q] permutes_inv_inv[OF r] show "q = r"
      by metis
  qed
  have th1: "?inv ` ?S = ?S"
    using image_inverse_permutations by blast
  have th2: "?rhs = finsum R (f \<circ> ?inv) ?S"
    by (simp add: o_def)
  from finsum_reindex[OF _ th0, of f] show ?thesis unfolding th1 th2 using f .
qed

lemma finsum_permutations_compose_right: assumes q: "q permutes S"
  and *: "f \<in> {p. p permutes S} \<rightarrow> carrier R"
  shows "finsum R f {p. p permutes S} = finsum R (\<lambda>p. f(p \<circ> q)) {p. p permutes S}"
  (is "?lhs = ?rhs")
proof -
  let ?S = "{p. p permutes S}"
  let ?inv = "Hilbert_Choice.inv"
  have th0: "?rhs = finsum R (f \<circ> (\<lambda>p. p \<circ> q)) ?S"
    by (simp add: o_def)
  have th1: "inj_on (\<lambda>p. p \<circ> q) ?S"
  proof (auto simp add: inj_on_def)
    fix p r
    assume "p permutes S"
      and r: "r permutes S"
      and rp: "p \<circ> q = r \<circ> q"
    then have "p \<circ> (q \<circ> ?inv q) = r \<circ> (q \<circ> ?inv q)"
      by (simp add: o_assoc)
    with permutes_surj[OF q, unfolded surj_iff] show "p = r"
      by simp
  qed
  have th3: "(\<lambda>p. p \<circ> q) ` ?S = ?S"
    using image_compose_permutations_right[OF q] by auto
  from finsum_reindex[OF _ th1, of f]
  show ?thesis unfolding th0 th1 th3 using * .
qed

end

end
