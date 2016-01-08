(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Missing Vector Spaces\<close>

text \<open>This theory provides some lemmas which we required when working with vector spaces.\<close>  

theory Missing_VectorSpace
imports 
  "../VectorSpace/VectorSpace"
begin

lemma Diff_not_in: "a \<notin> A - {a}" by auto

context abelian_group begin

lemma finsum_restrict:
  assumes fA: "f : A \<rightarrow> carrier G"
      and restr: "restrict f A = restrict g A"
  shows "finsum G f A = finsum G g A"
proof (rule finsum_cong';rule?)
  fix a assume a: "a : A"
  have "f a = restrict f A a" using a by simp
  also have "... = restrict g A a" using restr by simp
  also have "... = g a" using a by simp
  finally show "f a = g a".
  thus "g a : carrier G" using fA a by force
qed

lemma minus_nonzero: "x : carrier G \<Longrightarrow> x \<noteq> \<zero> \<Longrightarrow> \<ominus> x \<noteq> \<zero>"
  using minus_minus by fastforce

end

lemma (in ordered_comm_monoid_add) positive_sum:
  assumes X : "finite X"
      and "f : X \<rightarrow> { y :: 'a. y \<ge> 0 }"
  shows "setsum f X \<ge> 0 \<and> (setsum f X = 0 \<longrightarrow> f ` X \<subseteq> {0})"
  using assms
proof (induct set:finite)
  case (insert x X)
    hence x0: "f x \<ge> 0" and sum0: "setsum f X \<ge> 0" by auto
    hence "setsum f (insert x X) \<ge> 0" using insert by auto
    moreover
    { assume "setsum f (insert x X) = 0"
      hence "f x = 0" "setsum f X = 0"
        using sum0 x0 insert add_nonneg_eq_0_iff by auto
    }
    ultimately show ?case using insert by blast
qed auto


lemma insert_union: "insert x X = X \<union> {x}" by auto


context vectorspace begin

lemmas lincomb_insert2 = lincomb_insert[unfolded insert_union[symmetric]]

lemma lincomb_restrict:
  assumes U: "U \<subseteq> carrier V"
      and a: "a : U \<rightarrow> carrier K"
      and restr: "restrict a U = restrict b U"
  shows "lincomb a U = lincomb b U"
proof -
  let ?f = "\<lambda>a u. a u \<odot>\<^bsub>V\<^esub> u"
  have fa: "?f a : U \<rightarrow> carrier V" using a U by auto
  have "restrict (?f a) U = restrict (?f b) U"
  proof
    fix u
    have "u : U \<Longrightarrow> a u = b u" using restr unfolding restrict_def by metis
    thus "restrict (?f a) U u = restrict (?f b) U u" by auto
  qed
  thus ?thesis
    unfolding lincomb_def using finsum_restrict[OF fa] by auto
qed

lemma lindep_span:
  assumes U: "U \<subseteq> carrier V" and finU: "finite U"
  shows "lin_dep U = (\<exists>u \<in> U. u \<in> span (U - {u}))" (is "?l = ?r")
proof
  assume l: "?l" show "?r"
  proof -
    from l[unfolded lin_dep_def]
    obtain A a u
    where finA: "finite A"
      and AU: "A \<subseteq> U"
      and aA: "a : A \<rightarrow> carrier K"
      and aA0: "lincomb a A = zero V"
      and uA: "u:A"
      and au0: "a u \<noteq> zero K" by auto
    def a'\<equiv> "\<lambda>v. (if v : A then a v else zero K)"
    have a'U: "a' : U \<rightarrow> carrier K" unfolding a'_def using aA by auto
    have uU: "u : U" using uA AU by auto
    have a'u0: "a' u \<noteq> zero K" unfolding a'_def using au0 uA by auto
    def B \<equiv> "U - A"
    have B: "B \<subseteq> carrier V" unfolding B_def using U by auto
    have UAB: "U = A \<union> B" unfolding B_def using AU by auto
    have finB: "finite B" using finU B_def by auto
    have AB: "A \<inter> B = {}" unfolding B_def by auto
    let ?f = "\<lambda>v. a v \<odot>\<^bsub>V\<^esub> v"
    have fA: "?f : A \<rightarrow> carrier V" unfolding a'_def using aA AU U by auto
    let ?f' = "\<lambda>v. a' v \<odot>\<^bsub>V\<^esub> v"
    have "restrict ?f A = restrict ?f' A" unfolding a'_def by auto
    hence finsum: "finsum V ?f' A = finsum V ?f A"
      using finsum_restrict[OF fA] by simp
    have f'A: "?f' : A \<rightarrow> carrier V"
    proof
      fix x assume xA: "x \<in> A"
      show "?f' x : carrier V" unfolding a'_def using aA xA AU U by auto
    qed
    have f'B: "?f' : B \<rightarrow> carrier V"
    proof
      fix x assume xB: "x : B"
      have "x \<notin> A" using a'U xB unfolding B_def by auto
      thus "?f' x : carrier V"using xB B unfolding a'_def by auto
    qed
    have sumB0: "finsum V ?f' B = zero V"
    proof -
      { fix B'
        have "finite B' \<Longrightarrow> B' \<subseteq> B \<Longrightarrow> finsum V ?f' B' = zero V"
        proof(induct set:finite)
          case (insert b B')
            have finB': "finite B'" and bB': "b \<notin> B'" using insert by auto
            have f'B': "?f' : B' \<rightarrow> carrier V" using f'B insert by auto
            have bA: "b \<notin> A" using insert unfolding B_def by auto
            have b: "b : carrier V" using insert B by auto
            have foo: "a' b \<odot>\<^bsub>V\<^esub> b \<in> carrier V" unfolding a'_def using bA b by auto
            have IH: "finsum V ?f' B' = zero V" using insert by auto
            show ?case
              unfolding finsum_insert[OF finB' bB' f'B' foo]
              using IH a'_def bA b by auto
         qed auto
      }
      thus ?thesis using finB by auto
    qed
    have a'A0: "lincomb a' U = zero V"
      unfolding UAB
      unfolding lincomb_def 
      unfolding finsum_Un_disjoint[OF finA finB AB f'A f'B]
      unfolding finsum
      unfolding aA0[unfolded lincomb_def]
      unfolding sumB0 by simp
    have uU: "u:U" using uA AU by auto
    moreover have "u : span (U - {u})"
      using lincomb_isolate(2)[OF finU U a'U uU a'u0 a'A0].
    ultimately show ?r by auto
  qed
  next assume r: "?r" show "?l"
  proof -
    from r obtain u where uU: "u : U" and uspan: "u : span (U-{u})" by auto
    hence u: "u : carrier V" using U by auto
    have finUu: "finite (U-{u})" using finU by auto
    have Uu: "U-{u} \<subseteq> carrier V" using U by auto
    obtain a
      where ulin: "u = lincomb a (U-{u})"
        and a: "a : U-{u} \<rightarrow> carrier K"
      using uspan unfolding finite_span[OF finUu Uu] by auto
    show "?l" unfolding lin_dep_def
    proof(intro exI conjI)
      let ?a = "\<lambda>v. if v = u then \<ominus>\<^bsub>K\<^esub> one K else a v"
      show "?a : U \<rightarrow> carrier K" using a by auto
      hence a': "?a : U-{u}\<union>{u} \<rightarrow> carrier K" by auto
      have "U = U-{u}\<union>{u}" using uU by auto
      also have "lincomb ?a ... = ?a u \<odot>\<^bsub>V\<^esub> u \<oplus>\<^bsub>V\<^esub> lincomb ?a (U-{u})"
        unfolding lincomb_insert[OF finUu Uu a' Diff_not_in u] by auto
      also have "restrict a (U-{u}) = restrict ?a (U-{u})" by auto
        hence "lincomb ?a (U-{u}) = lincomb a (U-{u})"
          using lincomb_restrict[OF Uu a] by auto
      also have "?a u \<odot>\<^bsub>V\<^esub> u = \<ominus>\<^bsub>V\<^esub> u" using smult_minus_1[OF u] by simp
      also have "lincomb a (U-{u}) = u" using ulin..
      also have "\<ominus>\<^bsub>V\<^esub> u \<oplus>\<^bsub>V\<^esub> u = zero V" using l_neg[OF u].
      finally show "lincomb ?a U = zero V" by auto
    qed (insert uU finU, auto)
  qed
qed

lemma not_lindepD:
  assumes "~ lin_dep S"
      and "finite A" "A \<subseteq> S" "f : A \<rightarrow> carrier K" "lincomb f A = zero V"
    shows "f : A \<rightarrow> {zero K}"
  using assms unfolding lin_dep_def by blast


lemma span_mem:
  assumes E: "E \<subseteq> carrier V" and uE: "u : E" shows "u : span E"
  unfolding span_def
proof (rule,intro exI conjI)
  show "u = lincomb (\<lambda>_. one K) {u}" unfolding lincomb_def using uE E by auto
  show "{u} \<subseteq> E" using uE by auto
qed auto

lemma lincomb_distrib:
  assumes U: "U \<subseteq> carrier V"
      and a: "a : U \<rightarrow> carrier K"
      and c: "c : carrier K"
  shows "c \<odot>\<^bsub>V\<^esub> lincomb a U = lincomb (\<lambda>u. c \<otimes>\<^bsub>K\<^esub> a u) U"
    (is "_ = lincomb ?b U")
  using U a
proof (induct U rule: infinite_finite_induct)
  case empty show ?case unfolding lincomb_def using c by simp next
  case (insert u U)
    then have U: "U \<subseteq> carrier V"
          and u: "u : carrier V"
          and a: "a : insert u U \<rightarrow> carrier K"
          and finU: "finite U" by auto
    hence aU: "a : U \<rightarrow> carrier K" by auto
    have b: "?b : insert u U \<rightarrow> carrier K" using a c by auto
    show ?case
      unfolding lincomb_insert2[OF finU U a `u\<notin>U` u]
      unfolding lincomb_insert2[OF finU U b `u\<notin>U` u]
      using insert U aU c u smult_r_distr smult_assoc1 by auto next
  case (infinite U)
    thus ?case unfolding lincomb_def using assms by simp
qed

lemma span_swap:
  assumes finE[simp]: "finite E"
      and E[simp]: "E \<subseteq> carrier V"
      and u[simp]: "u : carrier V"
      and usE: "u \<notin> span E"
      and v[simp]: "v : carrier V"
      and usEv: "u : span (insert v E)"
  shows "span (insert u E) \<subseteq> span (insert v E)" (is "?L \<subseteq> ?R")
proof -
  have Eu[simp]: "insert u E \<subseteq> carrier V" by auto
  have Ev[simp]: "insert v E \<subseteq> carrier V" by auto
  have finEu: "finite (insert u E)" and finEv: "finite (insert v E)"
    using finE by auto
  have uE: "u \<notin> E" using usE span_mem by force
  have vE: "v \<notin> E" 
  proof
    assume "v : E"
    hence EvE: "insert v E = E" using insert_absorb by auto
    hence "u : span E" using usEv by auto
    thus "False" using usE by auto
  qed
  obtain ua
    where ua[simp]: "ua : (insert v E) \<rightarrow> carrier K"
      and uua: "u = lincomb ua (insert v E)"
    using usEv finite_span[OF finEv Ev]  by auto
  hence uaE[simp]: "ua : E \<rightarrow> carrier K" and [simp]: "ua v : carrier K"
    by auto

  show "?L \<subseteq> ?R"
  proof
    fix x assume "x : ?L"
    then obtain xa
    where xa: "xa : insert u E \<rightarrow> carrier K"
      and xxa: "x = lincomb xa (insert u E)"
      unfolding finite_span[OF finEu Eu] by auto
    hence xaE[simp]: "xa : E \<rightarrow> carrier K" and xau[simp]: "xa u : carrier K" by auto
    show "x : span (insert v E)"
      unfolding finite_span[OF finEv Ev]
    proof (rule,intro exI conjI)
      def a \<equiv> "\<lambda>e. xa u \<otimes>\<^bsub>K\<^esub> ua e"
      def a' \<equiv> "\<lambda>e. a e \<oplus>\<^bsub>K\<^esub> xa e"
      def a'' \<equiv> "\<lambda>e. if e = v then xa u \<otimes>\<^bsub>K\<^esub> ua v else a' e"
      have aE: "a : E \<rightarrow> carrier K" unfolding a_def using xau uaE u by blast
      hence a'E: "a' : E \<rightarrow> carrier K" unfolding a'_def using xaE by blast
      thus a'': "a'' : insert v E \<rightarrow> carrier K" unfolding a''_def by auto
      have restr: "restrict a' E = restrict a'' E"
        unfolding a''_def using vE by auto
      have "x = xa u \<odot>\<^bsub>V\<^esub> u \<oplus>\<^bsub>V\<^esub> lincomb xa E"
        using xxa lincomb_insert2 finE E xa uE u by auto
      also have
        "xa u \<odot>\<^bsub>V\<^esub> u = xa u \<odot>\<^bsub>V\<^esub> lincomb ua (insert v E)"
        using uua by auto
      also have "lincomb ua (insert v E) = ua v \<odot>\<^bsub>V\<^esub> v \<oplus>\<^bsub>V\<^esub> lincomb ua E"
        using lincomb_insert2 finE E ua vE v by auto
      also have "xa u \<odot>\<^bsub>V\<^esub> ... = xa u \<odot>\<^bsub>V\<^esub> (ua v \<odot>\<^bsub>V\<^esub> v) \<oplus>\<^bsub>V\<^esub> xa u \<odot>\<^bsub>V\<^esub> lincomb ua E"
        using smult_r_distr by auto
      also have "xa u \<odot>\<^bsub>V\<^esub> lincomb ua E = lincomb a E"
        unfolding a_def using lincomb_distrib[OF E] by auto
      finally have "x = xa u \<odot>\<^bsub>V\<^esub> (ua v \<odot>\<^bsub>V\<^esub> v) \<oplus>\<^bsub>V\<^esub> (lincomb a E \<oplus>\<^bsub>V\<^esub> lincomb xa E)"
        using a_assoc xau v aE xaE by auto
      also have "lincomb a E \<oplus>\<^bsub>V\<^esub> lincomb xa E = lincomb a' E"
        unfolding a'_def using lincomb_sum[OF finE E aE xaE]..
      also have "... = lincomb a'' E"
        using lincomb_restrict[OF E a'E ] restr by auto
      finally have "x = ((xa u \<otimes>\<^bsub>K\<^esub> ua v) \<odot>\<^bsub>V\<^esub> v) \<oplus>\<^bsub>V\<^esub> lincomb a'' E"
        using smult_assoc1 by auto
      also have "xa u \<otimes>\<^bsub>K\<^esub> ua v = a'' v" unfolding a''_def by simp
      also have "(a'' v \<odot>\<^bsub>V\<^esub> v) \<oplus>\<^bsub>V\<^esub> lincomb a'' E = lincomb a'' (insert v E)"
        using lincomb_insert2[OF finE E a'' vE] by auto
      finally show "x = lincomb a'' (insert v E)".
    qed
  qed
qed

lemma basis_swap:
  assumes finE[simp]: "finite E"
      and u[simp]: "u : carrier V"
      and uE[simp]: "u \<notin> E"
      and b: "basis (insert u E)"
      and v[simp]: "v : carrier V"
      and uEv: "u : span (insert v E)"
  shows "basis (insert v E)"
  unfolding basis_def
proof (intro conjI)
  have Eu[simp]: "insert u E \<subseteq> carrier V"
   and spanEu: "carrier V = span (insert u E)"
   and indEu: "~ lin_dep (insert u E)"
    using b[unfolded basis_def] by auto
  hence E[simp]: "E \<subseteq> carrier V" by auto
  thus Ev[simp]: "insert v E \<subseteq> carrier V" using v by auto
  have finEu: "finite (insert u E)"
   and finEv: "finite (insert v E)" using finE by auto
  have usE: "u \<notin> span E"
  proof
    assume "u : span E"
    hence "u : span (insert u E - {u})" using uE by auto
    moreover have "u : insert u E" by auto
    ultimately have "lin_dep (insert u E)"
      unfolding lindep_span[OF Eu finEu] by auto
    thus "False" using b unfolding basis_def by auto
  qed

  obtain ua
    where ua[simp]: "ua : insert v E \<rightarrow> carrier K"
      and uua: "u = lincomb ua (insert v E)"
    using uEv finite_span[OF finEv Ev]  by auto
  hence uaE[simp]: "ua : E \<rightarrow> carrier K"
    and uav[simp]: "ua v : carrier K"
    by auto

  have vE: "v \<notin> E"
  proof
    assume "v : E"
    hence EvE: "insert v E = E" using insert_absorb by auto
    hence "u : span E" using uEv by auto
    thus "False" using usE by auto
  qed
  have vsE: "v \<notin> span E"
  proof
    assume "v : span E"
    then obtain va
      where va[simp]: "va : E \<rightarrow> carrier K"
        and vva: "v = lincomb va E"
      using finite_span[OF finE E] by auto
    def va' \<equiv> "\<lambda>e. ua v \<otimes>\<^bsub>K\<^esub> va e"
    def va'' \<equiv> "\<lambda>e. va' e \<oplus>\<^bsub>K\<^esub> ua e"
    have va'[simp]: "va' : E \<rightarrow> carrier K"
      unfolding va'_def using uav va by blast
    hence va''[simp]: "va'' : E \<rightarrow> carrier K"
      unfolding va''_def using ua by blast
    from uua
    have "u = ua v \<odot>\<^bsub>V\<^esub> v \<oplus>\<^bsub>V\<^esub> lincomb ua E"
      using lincomb_insert2 vE by auto
    also have "ua v \<odot>\<^bsub>V\<^esub> v = ua v \<odot>\<^bsub>V\<^esub> (lincomb va E)"
      using vva by auto
    also have "... = lincomb va' E"
      unfolding va'_def using lincomb_distrib by auto
    finally have "u = lincomb va'' E"
      unfolding va''_def
      using lincomb_sum[OF finE E] by auto
    hence "u : span E" using finite_span[OF finE E] va'' by blast
    hence "lin_dep (insert u E)" using lindep_span by simp
    then show False using indEu by auto
  qed

  have indE: "~ lin_dep E" using indEu subset_li_is_li by auto

  show "~ lin_dep (insert v E)" using lin_dep_iff_in_span[OF E indE v vE] vsE by auto

  show "span (insert v E) = carrier V" (is "?L = ?R")
  proof (rule)
    show "?L \<subseteq> ?R"
    proof
      have finEv: "finite (insert v E)" using finE by auto
      fix x assume "x : ?L"
      then obtain a
        where a: "a : insert v E \<rightarrow> carrier K"
          and x: "x = lincomb a (insert v E)"
        unfolding finite_span[OF finEv Ev] by auto
      from a have av: "a v : carrier K" by auto
      from a have a2: "a : E \<rightarrow> carrier K" by auto
      show "x : ?R"
        unfolding x
        unfolding lincomb_insert2[OF finE E a vE v]
        using lincomb_closed[OF E a2] av v
        by auto
    qed
    show "?R \<subseteq> ?L"
      using span_swap[OF finE E u usE v uEv] spanEu by auto
  qed
qed

lemma span_empty: "span {} = {zero V}"
  unfolding finite_span[OF finite.emptyI empty_subsetI]
  unfolding lincomb_def by simp

lemma span_self: assumes [simp]: "v : carrier V" shows "v : span {v}"
proof -
  have "v = lincomb (\<lambda>x. one K) {v}" unfolding lincomb_def by auto
  thus ?thesis using finite_span by auto
qed

lemma span_zero: "zero V : span U" unfolding span_def lincomb_def by force

definition emb where "emb f D x = (if x : D then f x else zero K)"

lemma emb_carrier[simp]: "f : D \<rightarrow> R \<Longrightarrow> emb f D : D \<rightarrow> R"
  apply rule unfolding emb_def by auto

lemma emb_restrict: "restrict (emb f D) D = restrict f D"
  apply rule unfolding restrict_def emb_def by auto

lemma emb_zero: "emb f D : X - D \<rightarrow> { zero K }"
  apply rule unfolding emb_def by auto

lemma lincomb_clean:
  assumes A: "A \<subseteq> carrier V"
    and Z: "Z \<subseteq> carrier V"
    and finA: "finite A"
    and finZ: "finite Z"
    and aA: "a : A \<rightarrow> carrier K"
    and aZ: "a : Z \<rightarrow> { zero K }"
  shows "lincomb a (A \<union> Z) = lincomb a A"
  using finZ Z aZ
proof(induct set:finite)
  case empty thus ?case by simp next
  case (insert z Z) show ?case
    proof (cases "z : A")
      case True hence "A \<union> insert z Z = A \<union> Z" by auto
        thus ?thesis using insert by simp next
      case False
        have finAZ: "finite (A \<union> Z)" using finA insert by simp
        have AZ: "A \<union> Z \<subseteq> carrier V" using A insert by simp
        have a: "a : insert z (A \<union> Z) \<rightarrow> carrier K" using insert aA by force
        have "a z = zero K" using insert by auto
        also have "... \<odot>\<^bsub>V\<^esub> z = zero V" using insert by auto
        also have "... \<oplus>\<^bsub>V\<^esub> lincomb a (A \<union> Z) = lincomb a (A \<union> Z)"
          using insert AZ aA by auto
        also have "... = lincomb a A" using insert by simp
        finally have "a z \<odot>\<^bsub>V\<^esub> z \<oplus>\<^bsub>V\<^esub> lincomb a (A \<union> Z) = lincomb a A".
        thus ?thesis
          using lincomb_insert2[OF finAZ AZ a] False insert by auto 
    qed
qed

lemma span_add1:
  assumes U: "U \<subseteq> carrier V" and v: "v : span U" and w: "w : span U"
  shows "v \<oplus>\<^bsub>V\<^esub> w : span U"
proof -
  from v obtain a A
    where finA: "finite A"
      and va: "lincomb a A = v"
      and AU: "A \<subseteq> U"
      and a: "a : A \<rightarrow> carrier K"
    unfolding span_def by auto
  hence A: "A \<subseteq> carrier V" using U by auto
  from w obtain b B
    where finB: "finite B"
      and wb: "lincomb b B = w"
      and BU: "B \<subseteq> U"
      and b: "b : B \<rightarrow> carrier K"
    unfolding span_def by auto
  hence B: "B \<subseteq> carrier V" using U by auto

  have B_A: "B - A \<subseteq> carrier V" and A_B: "A - B \<subseteq> carrier V" using A B by auto

  have a': "emb a A : A \<union> B \<rightarrow> carrier K"
    apply (rule Pi_I) unfolding emb_def using a by auto
  hence a'A: "emb a A : A \<rightarrow> carrier K" by auto
  have a'Z: "emb a A : B - A \<rightarrow> { zero K }"
    apply (rule Pi_I) unfolding emb_def using a by auto

  have b': "emb b B : A \<union> B \<rightarrow> carrier K"
    apply (rule Pi_I) unfolding emb_def using b by auto
  hence b'B: "emb b B : B \<rightarrow> carrier K" by auto
  have b'Z: "emb b B : A - B \<rightarrow> { zero K }"
    apply (rule Pi_I) unfolding emb_def using b by auto

  show ?thesis
    unfolding span_def
    proof (rule,intro exI conjI)
      let ?v = "lincomb (emb a A) (A \<union> B)"
      let ?w = "lincomb (emb b B) (A \<union> B)"
      let ?ab = "\<lambda>u. (emb a A) u \<oplus>\<^bsub>K\<^esub> (emb b B) u"
      show finAB: "finite (A \<union> B)" using finA finB by auto
      show "A \<union> B \<subseteq> U" using AU BU by auto
      show "?ab : A \<union> B \<rightarrow> carrier K" using a' b' by auto
      have "v = ?v"
        using va lincomb_restrict[OF A a emb_restrict[symmetric]]
        using lincomb_clean[OF A B_A] a'A a'Z finA finB by simp
      moreover have "w = ?w"
        apply (subst Un_commute)
        using wb lincomb_restrict[OF B b emb_restrict[symmetric]]
        using lincomb_clean[OF B A_B] finA finB b'B b'Z by simp
      ultimately show "v \<oplus>\<^bsub>V\<^esub> w = lincomb ?ab (A \<union> B)"
        using lincomb_sum[OF finAB] A B a' b' by simp
    qed
qed

lemma span_neg:
  assumes U: "U \<subseteq> carrier V" and vU: "v : span U"
  shows "\<ominus>\<^bsub>V\<^esub> v : span U"
proof -
  have v: "v : carrier V" using vU U unfolding span_def by auto
  from vU[unfolded span_def]
  obtain a A
    where finA: "finite A"
      and AU: "A \<subseteq> U"
      and a: "a \<in> A \<rightarrow> carrier K"
      and va: "v = lincomb a A" by auto
  hence A: "A \<subseteq> carrier V" using U by simp
  let ?a = "\<lambda>u. \<ominus>\<^bsub>K\<^esub> one K \<otimes>\<^bsub>K\<^esub> a u"

  have "\<ominus>\<^bsub>V\<^esub> v = \<ominus>\<^bsub>K\<^esub> one K \<odot>\<^bsub>V\<^esub> v" using smult_minus_1_back[OF v].
  also have "... = \<ominus>\<^bsub>K\<^esub> one K \<odot>\<^bsub>V\<^esub> lincomb a A" using va by simp
  finally have main: "\<ominus>\<^bsub>V\<^esub> v = lincomb ?a A"
    unfolding lincomb_distrib[OF A a R.a_inv_closed[OF R.one_closed]] by auto
  show ?thesis
    unfolding span_def
    apply rule
    using main a finA AU by force
qed

lemma span_closed[simp]: "U \<subseteq> carrier V \<Longrightarrow> v : span U \<Longrightarrow> v : carrier V"
  unfolding span_def by auto

lemma span_add:
  assumes U: "U \<subseteq> carrier V" and vU: "v : span U" and w[simp]: "w : carrier V"
  shows "w : span U \<longleftrightarrow> v \<oplus>\<^bsub>V\<^esub> w : span U" (is "?L \<longleftrightarrow> ?R")
proof
  show "?L \<Longrightarrow> ?R" using span_add1[OF U vU] by auto
  assume R: "?R" show "?L"
  proof -
    have v[simp]: "v : carrier V" using vU U by simp
    have "w = zero V \<oplus>\<^bsub>V\<^esub> w" using M.l_zero by auto
    also have "... = \<ominus>\<^bsub>V\<^esub> v \<oplus>\<^bsub>V\<^esub> v \<oplus>\<^bsub>V\<^esub> w" using M.l_neg by auto
    also have "... = \<ominus>\<^bsub>V\<^esub> v \<oplus>\<^bsub>V\<^esub> (v \<oplus>\<^bsub>V\<^esub> w)"
      using M.l_zero M.a_assoc M.a_closed by auto
    also have "... : span U" using span_neg[OF U vU] span_add1[OF U] R by auto
    finally show ?thesis.
  qed
qed


lemma lincomb_union:
  assumes U: "U \<subseteq> carrier V"
      and U'[simp]: "U' \<subseteq> carrier V"
      and disj: "U \<inter> U' = {}"
      and finU: "finite U"
      and finU': "finite U'"
      and a: "a : U \<union> U' \<rightarrow> carrier K"
    shows "lincomb a (U \<union> U') = lincomb a U \<oplus>\<^bsub>V\<^esub> lincomb a U'"
  using finU U disj a
proof (induct set:finite)
  case empty thus ?case by (subst(2) lincomb_def, simp) next
  case (insert u U) thus ?case
    unfolding Un_insert_left
    using lincomb_insert2 finU' insert a_assoc by auto
qed

lemma span_union1:
  assumes U: "U \<subseteq> carrier V" and U': "U' \<subseteq> carrier V" and UU': "span U = span U'"
      and W: "W \<subseteq> carrier V" and W': "W' \<subseteq> carrier V" and WW': "span W = span W'"
  shows "span (U \<union> W) \<subseteq> span (U' \<union> W')" (is "?L \<subseteq> ?R")
proof
  fix x assume "x : ?L"
  then obtain a A
    where finA: "finite A"
      and AUW: "A \<subseteq> U \<union> W"
      and x: "x = lincomb a A"
      and a: "a : A \<rightarrow> carrier K"
    unfolding span_def by auto
  let ?AU = "A \<inter> U" and ?AW = "A \<inter> W - U"
  have AU: "?AU \<subseteq> carrier V" using U by auto
  have AW: "?AW \<subseteq> carrier V" using W by auto
  have disj: "?AU \<inter> ?AW = {}" by auto
  have U'W': "U' \<union> W' \<subseteq> carrier V" using U' W' by auto

  have "?AU \<union> ?AW = A" using AUW by auto
  hence "x = lincomb a (?AU \<union> ?AW)" using x by auto
  hence "x = lincomb a ?AU \<oplus>\<^bsub>V\<^esub> lincomb a ?AW"
    using lincomb_union[OF AU AW disj] finA a by auto
  moreover
    have "lincomb a ?AU : span U" and "lincomb a ?AW : span W"
      unfolding span_def using AU a finA by auto
    hence "lincomb a ?AU : span U'" and "lincomb a ?AW : span W'"
      using UU' WW' by auto
    hence "lincomb a ?AU : ?R" and "lincomb a ?AW : ?R"
      using span_is_monotone[OF Un_upper1, of U']
      using span_is_monotone[OF Un_upper2, of W'] by auto
  ultimately
    show "x : ?R" using span_add1[OF U'W'] by auto 
qed

lemma span_union:
  assumes U: "U \<subseteq> carrier V" and U': "U' \<subseteq> carrier V" and UU': "span U = span U'"
      and W: "W \<subseteq> carrier V" and W': "W' \<subseteq> carrier V" and WW': "span W = span W'"
  shows "span (U \<union> W) = span (U' \<union> W')" (is "?L = ?R")
  using span_union1[OF assms]
  using span_union1[OF U' U UU'[symmetric] W' W WW'[symmetric]]
  by auto

lemma lincomb_zero:
  assumes U: "U \<subseteq> carrier V" and a: "a : U \<rightarrow> {zero K}"
  shows "lincomb a U = zero V"
  using U a
proof (induct U rule: infinite_finite_induct)
  case empty show ?case unfolding lincomb_def by auto next
  case (insert u U)
    hence "a \<in> insert u U \<rightarrow> carrier K" using zero_closed by force
    thus ?case using insert by (subst lincomb_insert2; auto)
qed (auto simp: lincomb_def)

end

end
