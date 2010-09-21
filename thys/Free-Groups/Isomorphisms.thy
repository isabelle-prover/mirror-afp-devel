header {* Isomorphisms of Free Groups *}

theory "Isomorphisms"
imports
   "UnitGroup"
   "~~/src/HOL/Algebra/IntRing"
   "FreeGroups"
   C2
begin

subsection {* The Free Group over the empty set *}

text {* The Free Group over an empty set of generators is isomorphic to the trivial
group. *}

lemma free_group_over_empty_set: "\<exists>h. h \<in> \<F>\<^bsub>{}\<^esub> \<cong> unit_group"
proof(rule group.unit_group_unique)
  show "group \<F>\<^bsub>{}\<^esub>" by (rule free_group_is_group)
next
  have "carrier \<F>\<^bsub>{}::'a set\<^esub> = {[]}"
    by(auto simp add:free_group_def occuring_generators_def)
  thus "card (carrier \<F>\<^bsub>{}::'a set\<^esub>) = 1"
    by simp
qed

subsection {* The Free Group over one generator *}

text {* The Free Group over one generator is isomorphic to the free abelian group
over one element, also known as the integers. *}

abbreviation "int_group"
  where "int_group \<equiv> \<lparr> carrier = carrier \<Z>, mult = op +, one = 0::int \<rparr>"

lemma replicate_set_eq[simp]: "\<forall>x \<in> set xs. x = y \<Longrightarrow> xs = replicate (length xs) y"
  by(induct xs)auto

lemma int_group_gen_by_one: "\<langle>{1}\<rangle>\<^bsub>int_group\<^esub> = carrier int_group"
proof
  show "\<langle>{1}\<rangle>\<^bsub>int_group\<^esub> \<subseteq> carrier int_group"
    by auto
  show "carrier int_group \<subseteq> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>"
  proof
    interpret int: group int_group by (rule int.a_group)
    fix x
    have plus1: "1 \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>"
      by (auto intro:gen_span.gen_gens)
    hence "inv\<^bsub>int_group\<^esub> 1 \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>"
      by (auto intro:gen_span.gen_inv)
    moreover
    have "-1 = inv\<^bsub>int_group\<^esub> 1" 
      by (auto intro: int.inv_equality)
    ultimately
    have minus1: "-1 \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>"
      by (simp)

    show "x \<in> \<langle>{1::int}\<rangle>\<^bsub>int_group\<^esub>" (*
    It does not work directly, unfortunately:
    apply(induct x rule:int_induct[of _ "0::int"])
    apply (auto simp add: int_arith_rules intro:gen_span.intros[of int_group])
    *)
    proof(induct x rule:int_induct[of _ "0::int"])
    case base
      have "\<one>\<^bsub>int_group\<^esub> \<in> \<langle>{1\<Colon>int}\<rangle>\<^bsub>int_group\<^esub>"
        by (rule gen_span.gen_one)
      thus"0 \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>"
        by simp
    next
    case (step1 i)
      from `i \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>` and plus1
      have "i \<otimes>\<^bsub>int_group\<^esub> 1 \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>" 
        by (rule gen_span.gen_mult)
      thus "i + 1 \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>" by simp
    next
    case (step2 i)
      from `i \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>` and minus1
      have "i \<otimes>\<^bsub>int_group\<^esub> -1 \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>" 
        by (rule gen_span.gen_mult)
      thus "i - 1 \<in> \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>" 
        by (simp add: int_arith_rules)
    qed
  qed
qed

lemma free_group_over_one_gen: "\<exists>h. h \<in> \<F>\<^bsub>{()}\<^esub> \<cong> int_group"
proof-
  interpret int: group int_group by (rule int.a_group)

  def f \<equiv> "\<lambda>(x::unit).(1::int)"
  have "f \<in> {()} \<rightarrow> carrier int_group"
    by auto
  hence "int.lift f \<in> hom \<F>\<^bsub>{()}\<^esub> int_group"
    by (rule int.lift_is_hom)
  then
  interpret hom: group_hom "\<F>\<^bsub>{()}\<^esub>" int_group "int.lift f"
    unfolding group_hom_def group_hom_axioms_def
    by(auto intro: int.a_group free_group_is_group)
    
  { (* This shows injectiveness of the given map *)
    fix x
    assume "x \<in> carrier \<F>\<^bsub>{()}\<^esub>"
    hence "canceled x" by (auto simp add:free_group_def)
    assume "int.lift f x = (0::int)"
    have "x = []" 
    proof(rule ccontr)
      assume "x \<noteq> []"
      then obtain a and xs where "x = a # xs" by (cases x, auto)
      hence "length (takeWhile (\<lambda>y. y = a) x) > 0" by auto
      then obtain i where i: "length (takeWhile (\<lambda>y. y = a) x) = Suc i" 
        by (cases "length (takeWhile (\<lambda>y. y = a) x)", auto)
      have "Suc i \<ge> length x"
      proof(rule ccontr)
        assume "\<not> length x \<le> Suc i"
        hence "length (takeWhile (\<lambda>y. y = a) x) < length x" using i by simp
        hence "\<not> (\<lambda>y. y = a) (x ! length (takeWhile (\<lambda>y. y = a) x))"
          by (rule nth_length_takeWhile)
        hence "\<not> (\<lambda>y. y = a) (x ! Suc i)" using i by simp
        hence "fst (x ! Suc i) \<noteq> fst a" by (cases "x ! Suc i", cases "a", auto)
        moreover
        {
          have "takeWhile (\<lambda>y. y = a) x ! i = x ! i"
            using i by (auto intro: takeWhile_nth)
          moreover
          have "(takeWhile (\<lambda>y. y = a) x) ! i \<in> set (takeWhile (\<lambda>y. y = a) x)"
            using i by auto
          ultimately
          have "(\<lambda>y. y = a) (x ! i)"
            by (auto dest:set_takeWhileD)
        }
        hence "fst (x ! i) = fst a" by auto
        moreover
        have "snd (x ! i) = snd (x ! Suc i)" by simp
        ultimately
        have "canceling (x ! i) (x ! Suc i)" unfolding canceling_def by auto
        hence "cancels_to_1_at i x (cancel_at i x)"
          using `\<not> length x \<le> Suc i` unfolding cancels_to_1_at_def 
          by (auto simp add:length_takeWhile_le)
        hence "cancels_to_1 x (cancel_at i x)" unfolding cancels_to_1_def by auto
        hence "\<not> canceled x" unfolding canceled_def by auto
        thus False using `canceled x` by contradiction
      qed
      hence "length (takeWhile (\<lambda>y. y = a) x) = length x"
        using i[THEN sym] by (auto dest:le_antisym simp add:length_takeWhile_le)
      hence "takeWhile (\<lambda>y. y = a) x = x"
        by (subst takeWhile_eq_take, simp)
      moreover
      have "\<forall>y \<in> set (takeWhile (\<lambda>y. y = a) x). y = a"
        by (auto dest: set_takeWhileD)
      ultimately
      have "\<forall>y \<in> set x. y = a" by auto
      hence "x = replicate (length x) a" by simp
      hence "int.lift f x = int.lift f (replicate (length x) a)" by simp
      also have "... = pow int_group (int.lift_gi f a) (length x)"
        by (induct x,auto simp add:int.lift_def)
      also have "... = (int.lift_gi f a) * int (length x)"
        by (induct ("length x"), auto simp add:int_distrib)
      finally have "\<dots> = 0" using `int.lift f x = 0` by simp
      hence "nat (abs (group.lift_gi int_group f a * int (length x))) = 0" by simp
      hence "nat (abs (group.lift_gi int_group f a)) * length x = 0" by simp
      hence "nat (abs (group.lift_gi int_group f a)) = 0"
        using `x \<noteq> []` by auto
      moreover
      have "inv\<^bsub>int_group\<^esub> 1 = -1" 
        by (auto intro: int.inv_equality)
      hence "abs (group.lift_gi int_group f a) = 1"
      using `group int_group`
        by(auto simp add: group.lift_gi_def f_def)
      ultimately
      show False by simp
    qed
  }
  hence "\<forall>x\<in>carrier \<F>\<^bsub>{()}\<^esub>. int.lift f x = \<one>\<^bsub>int_group\<^esub> \<longrightarrow> x = \<one>\<^bsub>\<F>\<^bsub>{()}\<^esub>\<^esub>"
    by (auto simp add:free_group_def)
  moreover
  {
    have "carrier \<F>\<^bsub>{()}\<^esub> = \<langle>insert`{()}\<rangle>\<^bsub>\<F>\<^bsub>{()}\<^esub>\<^esub>"
      by (rule gens_span_free_group[THEN sym])
    moreover
    have "carrier int_group = \<langle>{1}\<rangle>\<^bsub>int_group\<^esub>"
      by (rule int_group_gen_by_one[THEN sym])
    moreover
    have "int.lift f ` insert ` {()} = {1}"
      by (auto simp add: int.lift_def insert_def f_def int.lift_gi_def)   
    moreover
    have  "int.lift f ` \<langle>insert`{()}\<rangle>\<^bsub>\<F>\<^bsub>{()}\<^esub>\<^esub> = \<langle>int.lift f ` (insert `{()})\<rangle>\<^bsub>int_group\<^esub>"
      by (rule hom.hom_span, auto intro:insert_closed)
    ultimately
    have "int.lift f ` carrier \<F>\<^bsub>{()}\<^esub> = carrier int_group"
      by simp
  }
  ultimately
  have "int.lift f \<in> \<F>\<^bsub>{()}\<^esub> \<cong> int_group"
    using `int.lift f \<in> hom \<F>\<^bsub>{()}\<^esub> int_group`
    by (auto intro:group_isoI simp add:hom.hom_mult free_group_is_group int.is_group)
  thus ?thesis by auto
qed

subsection {* Free Groups over isomorphic sets of generators *}

text {* Free Groups are isomorphic if their set of generators are isomorphic. *}

definition lift_generator_function :: "('a \<Rightarrow> 'b) \<Rightarrow> (bool \<times> 'a) list \<Rightarrow> (bool \<times> 'b) list"
where "lift_generator_function f = map (prod_fun id f)"

theorem isomorphic_free_groups:
  assumes "bij_betw f gens1 gens2"
  shows "lift_generator_function f \<in> \<F>\<^bsub>gens1\<^esub> \<cong> \<F>\<^bsub>gens2\<^esub>"
unfolding lift_generator_function_def
proof(rule group_isoI)
  show "\<forall>x\<in>carrier \<F>\<^bsub>gens1\<^esub>.
       map (prod_fun id f) x = \<one>\<^bsub>\<F>\<^bsub>gens2\<^esub>\<^esub> \<longrightarrow> x = \<one>\<^bsub>\<F>\<^bsub>gens1\<^esub>\<^esub>"
    by(auto simp add:free_group_def)
next
  from `bij_betw f gens1 gens2` have "inj_on f gens1" by (auto simp:bij_betw_def)
  show "map (prod_fun id f) ` carrier \<F>\<^bsub>gens1\<^esub> = carrier \<F>\<^bsub>gens2\<^esub>"
  proof(rule Set.set_eqI,rule iffI)
    from `bij_betw f gens1 gens2` have "f ` gens1 = gens2" by (auto simp:bij_betw_def)
    fix x :: "(bool \<times> 'b) list"
    assume "x \<in> image (map (prod_fun id f)) (carrier \<F>\<^bsub>gens1\<^esub>)"
    then obtain y :: "(bool \<times> 'a) list" where "x = map (prod_fun id f) y"
                    and "y \<in> carrier \<F>\<^bsub>gens1\<^esub>" by auto
    from `y \<in> carrier \<F>\<^bsub>gens1\<^esub>`
    have "canceled y" and "occuring_generators y \<subseteq> gens1" by (auto simp add:free_group_def)
    hence "set (map snd y) \<subseteq> gens1" unfolding occuring_generators_def by simp

    from `x = map (prod_fun id f) y`
    have "occuring_generators x = occuring_generators (map (prod_fun id f) y)"
      by simp
    also have "... = set (map snd (map (prod_fun id f) y))"
      unfolding occuring_generators_def ..
    also have "\<dots> = set (map (snd \<circ> prod_fun id f) y)" by simp
    also have "\<dots> = set (map (f \<circ> snd) y)" by auto
    also have "\<dots> = set (map f (map snd y))" by auto
    also have "\<dots> = f ` set (map snd y)" by (simp only: set_map)
    also from `set (map snd y) \<subseteq> gens1`
         have "\<dots> \<subseteq> f ` gens1" by auto
    also from `image f gens1 = gens2`
         have  "\<dots> \<subseteq> gens2" by simp
    finally
    have "occuring_generators x \<subseteq> gens2" .
    moreover
    from `inj_on f gens1` and `occuring_generators y \<subseteq> gens1`
    have "inj_on f (occuring_generators y)" by -(rule subset_inj_on)
    with `canceled y` have "canceled (map (prod_fun id f) y)"
      by -(rule rename_gens_canceled)
    with `x = map (prod_fun id f) y` have "canceled x" by simp
    ultimately
    show "x \<in> carrier \<F>\<^bsub>gens2\<^esub>" by (simp add:free_group_def)
  next
    fix x
    assume "x \<in> carrier \<F>\<^bsub>gens2\<^esub>"
    hence "canceled x" and "occuring_generators x \<subseteq> gens2"
      unfolding free_group_def by auto
    def y \<equiv> "map (prod_fun id (the_inv_into gens1 f)) x"
    have "map (prod_fun id f) y =
          map (prod_fun id f) (map (prod_fun id (the_inv_into gens1 f)) x)"
      by (simp add:y_def)
    also have "\<dots> = map (prod_fun id f \<circ> prod_fun id (the_inv_into gens1 f)) x"
      by simp
    also have "\<dots> = map (prod_fun id (f \<circ> the_inv_into gens1 f)) x"
      by auto
    also have "\<dots> = map id x"
    proof(rule map_ext, rule impI)
      fix xa :: "bool \<times> 'b"
      assume "xa \<in> set x"
      from `occuring_generators x \<subseteq> gens2`
      have "set (map snd x) \<subseteq> gens2"
        unfolding occuring_generators_def .
      hence "snd ` set x \<subseteq> gens2" by (simp add: set_map)
      with `xa \<in> set x` have "snd xa \<in> gens2" by auto
      with `bij_betw f gens1 gens2` have "snd xa \<in> f`gens1"
        by (auto simp add: bij_betw_def)

      have "prod_fun id (f \<circ> the_inv_into gens1 f) xa
            = prod_fun id (f \<circ> the_inv_into gens1 f) (fst xa, snd xa)" by simp
      also have "\<dots> = (fst xa, f (the_inv_into gens1 f (snd xa)))"
        by (auto simp del:pair_collapse)
      also with `snd xa \<in> image f gens1` and `inj_on f gens1`
           have "\<dots> = (fst xa, snd xa)"
           by (auto elim:f_the_inv_into_f simp del:pair_collapse)
      also have "\<dots> = id xa" by simp
      finally show "prod_fun id (f \<circ> the_inv_into gens1 f) xa = id xa".
    qed
    also have "\<dots> = x" unfolding id_def by auto
    finally have "map (prod_fun id f) y = x".
    moreover
    {
      from `bij_betw f gens1 gens2`
      have "bij_betw (the_inv_into gens1 f) gens2 gens1" by (rule bij_betw_the_inv_into)
      hence "inj_on (the_inv_into gens1 f) gens2" by (rule bij_betw_imp_inj_on)
      with `occuring_generators x \<subseteq> gens2`
      have "inj_on (the_inv_into gens1 f) (occuring_generators x)" by -(rule subset_inj_on)
      with `canceled x`
      have "canceled y" unfolding y_def by-(rule rename_gens_canceled)
      moreover
      {
        have "occuring_generators y
              = set (map snd (map (prod_fun id (the_inv_into gens1 f)) x))"
          by (simp add:y_def occuring_generators_def)
        also have "\<dots> = set (map ((the_inv_into gens1 f) \<circ> snd) x)" by simp
        also have "\<dots> = set (map (the_inv_into gens1 f) (map snd x))" by simp
        also have "\<dots> = (the_inv_into gens1 f) ` set (map snd x)"
               by (auto simp del:map_map)
        also from `occuring_generators x \<subseteq> gens2`
             have "\<dots> \<subseteq> (the_inv_into gens1 f) ` gens2"
               by (auto simp add: occuring_generators_def)
        also from `bij_betw (the_inv_into gens1 f) gens2 gens1`
             have "\<dots> \<subseteq> gens1" by (simp add:bij_betw_def)
        finally have "occuring_generators y \<subseteq> gens1".
      }
      ultimately
      have "y \<in> carrier \<F>\<^bsub>gens1\<^esub>" by (simp add:free_group_def)
    }
    ultimately
    show "x \<in> map (prod_fun id f) ` carrier \<F>\<^bsub>gens1\<^esub>" by auto
  qed
next
  from `bij_betw f gens1 gens2` have "inj_on f gens1" by (auto simp:bij_betw_def)
  {
  fix x
  assume "x \<in> carrier \<F>\<^bsub>gens1\<^esub>"
  fix y
  assume "y \<in> carrier \<F>\<^bsub>gens1\<^esub>"

  from `x \<in> carrier \<F>\<^bsub>gens1\<^esub>` and `y \<in> carrier \<F>\<^bsub>gens1\<^esub>`
  have "occuring_generators x \<subseteq> gens1" and "occuring_generators y \<subseteq> gens1"
    by (auto simp add:occuring_gens_in_element)
  hence "occuring_generators (x@y) \<subseteq> gens1"
    by(auto simp add:occuring_generators_def)
  with `inj_on f gens1` have "inj_on f (occuring_generators (x@y))"
    by (rule subset_inj_on)

  have "map (prod_fun id f) (x \<otimes>\<^bsub>\<F>\<^bsub>gens1\<^esub>\<^esub> y)
       = map (prod_fun id f) (normalize (x@y))" by (simp add:free_group_def)
  also from `inj_on f (occuring_generators (x@y))`
       have "\<dots> = normalize (map (prod_fun id f) (x@y))"
       by(auto simp add:rename_gens_normalize[THEN sym])
  also have "\<dots> = normalize (map (prod_fun id f) x @ map (prod_fun id f) y)"
       by (auto)
  also have "\<dots> = map (prod_fun id f) x \<otimes>\<^bsub>\<F>\<^bsub>gens2\<^esub>\<^esub> map (prod_fun id f) y"
       by (simp add:free_group_def)
  finally have "map (prod_fun id f) (x \<otimes>\<^bsub>\<F>\<^bsub>gens1\<^esub>\<^esub> y) =
                map (prod_fun id f) x \<otimes>\<^bsub>\<F>\<^bsub>gens2\<^esub>\<^esub> map (prod_fun id f) y".
  }
  thus "\<forall>x\<in>carrier \<F>\<^bsub>gens1\<^esub>.
       \<forall>y\<in>carrier \<F>\<^bsub>gens1\<^esub>.
          map (prod_fun id f) (x \<otimes>\<^bsub>\<F>\<^bsub>gens1\<^esub>\<^esub> y) =
          map (prod_fun id f) x \<otimes>\<^bsub>\<F>\<^bsub>gens2\<^esub>\<^esub> map (prod_fun id f) y"
   by auto
qed (auto intro: free_group_is_group)

subsection {* Bases of isomorphic free groups *}

text {* 
Isomorphic free groups have bases of same cardinality. Here, this is proven
only for finite bases. For infinite bases, a lemma such as @{text cardinal_UN_le}
(which is part of the ZF logic) could be used to show that the free group has the
same cardinality as the set of generators.
  *}

text {*
The proof for the finite case uses the set of of homomorphisms from the free
group to the group with two elements, as suggested by Christian Sievers. The
definition of @{term hom} is not suitable for proofs about the cardinality of that
set, as its definition does not require extensionality. This is amended by the
following definition:
*}

definition homr
  where "homr G H = {h. h \<in> hom G H \<and> h \<in> extensional (carrier G)}"

lemma (in group_hom) restrict_hom[intro!]:
  shows "restrict h (carrier G) \<in> homr G H"
  unfolding homr_def and hom_def
  by (auto)

lemma extensional_restrict[simp]:
  "f \<in> extensional A \<Longrightarrow> restrict f A = f"
 by (rule extensionalityI[OF restrict_extensional]) auto


text {*
A lemma to prove bijectivity by proving the inverse.
*}

lemma bij_betw_by_inv:
  assumes "f \<in> A \<rightarrow> B"
      and "g \<in> B \<rightarrow> A"
      and g_f: "\<And>x. x\<in>A \<Longrightarrow> g (f x) = x"
      and f_g: "\<And>y. y\<in>B \<Longrightarrow> f (g y) = y"
  shows "bij_betw f A B"
unfolding bij_betw_def
proof
  show "inj_on f A"
  proof(induct rule: inj_onI)
  case (1 x1 x2)
    then have "g (f x1) = g (f x2)" by simp
    then show "x1 = x2" using g_f[OF 1(1)] and g_f[OF 1(2)] by simp
  qed
next
  have "f ` A \<subseteq> B" using `f \<in> A \<rightarrow> B` by auto
  moreover have "B \<subseteq> f ` A"
  proof
    fix y assume "y\<in>B"
    thus "y \<in> f`A" using f_g[OF `y\<in>B`] and `g \<in> B \<rightarrow> A`
      by (auto intro: rev_image_eqI[of "g y"])
  qed
  ultimately show "f ` A = B" by auto
qed

lemma hom_F_C2_Powerset:
  "\<exists> f. bij_betw f (Pow X) (homr (\<F>\<^bsub>X\<^esub>) C2)"
proof
  interpret F: group "\<F>\<^bsub>X\<^esub>" by (rule free_group_is_group)
  interpret C2: group C2 by (rule C2_is_group)
  let ?f = "\<lambda>S . restrict (C2.lift S) (carrier \<F>\<^bsub>X\<^esub>)"
  let ?f' = "\<lambda>h . X \<inter> (h \<circ> insert)"
  show "bij_betw ?f (Pow X) (homr (\<F>\<^bsub>X\<^esub>) C2)"
  proof(induct rule: bij_betw_by_inv[of ?f _ _ ?f'])
  case 1 show ?case
    proof
      fix S assume "S \<in> Pow X"
      interpret h: group_hom "\<F>\<^bsub>X\<^esub>" C2 "C2.lift S"
        by unfold_locales (auto intro: C2.lift_is_hom)
      show "?f S \<in> homr \<F>\<^bsub>X\<^esub> C2"
        by (rule h.restrict_hom)
     qed
  next
  case 2 show ?case by auto next
  case (3 S) show ?case
    proof (induct rule: Set.set_eqI)
      case (1 x) show ?case
      proof(cases "x \<in> X")
      case True thus ?thesis using insert_closed[of x X]
         by (auto simp add:insert_def C2.lift_def C2.lift_gi_def mem_def )
      next case False thus ?thesis using 3 by auto
    qed
  qed
  next
  case (4 h)
    hence hom: "h \<in> hom \<F>\<^bsub>X\<^esub> C2"
      and extn: "h \<in> extensional (carrier \<F>\<^bsub>X\<^esub>)"
      unfolding homr_def by auto
    have "\<forall>x \<in> carrier \<F>\<^bsub>X\<^esub> . h x = group.lift C2 (X \<inter> (h \<circ> FreeGroups.insert)) x"
     by (rule C2.lift_is_unique[OF C2_is_group _ hom, of "X \<inter> (h \<circ> FreeGroups.insert)"],
             auto simp add:mem_def)
    thus ?case
    by -(rule extensionalityI[OF restrict_extensional extn], auto)
  qed
qed

lemma group_iso_betw_hom:
  assumes "group G1" and "group G2"
      and iso: "i \<in> G1 \<cong> G2"
  shows   "\<exists> f . bij_betw f (homr G2 H) (homr G1 H)"
proof-
  interpret G2: group G2 by (rule `group G2`)
  let ?i' = "restrict (inv_into (carrier G1) i) (carrier G2)"
  have "inv_into (carrier G1) i \<in> G2 \<cong> G1" by (rule group.iso_sym[OF `group G1` iso])
  hence iso': "?i' \<in> G2 \<cong> G1"
    by (auto simp add:iso_def hom_def G2.m_closed)
  show ?thesis
  proof(rule, induct rule: bij_betw_by_inv[of "(\<lambda>h. compose (carrier G1) h i)" _ _ "(\<lambda>h. compose (carrier G2) h ?i')"])
  case 1
    show ?case
    proof
      fix h assume "h \<in> homr G2 H"
      hence "compose (carrier G1) h i \<in> hom G1 H"
        using iso
        by (auto intro: group.hom_compose[OF `group G1`, of _ G2] simp add:iso_def homr_def)
      thus "compose (carrier G1) h i \<in> homr G1 H"
        unfolding homr_def by simp
     qed
  next
  case 2
    show ?case
    proof
      fix h assume "h \<in> homr G1 H"
      hence "compose (carrier G2) h ?i' \<in> hom G2 H"
        using iso'
        by (auto intro: group.hom_compose[OF `group G2`, of _ G1] simp add:iso_def homr_def)
      thus "compose (carrier G2) h ?i' \<in> homr G2 H"
        unfolding homr_def by simp
     qed
  next
  case (3 x)
    hence "compose (carrier G2) (compose (carrier G1) x i) ?i'
          = compose (carrier G2) x (compose (carrier G2) i ?i')"
      using iso iso'
      by (auto intro: compose_assoc[THEN sym]   simp add:iso_def hom_def homr_def)
    also have "\<dots> = compose (carrier G2) x (\<lambda>y\<in>carrier G2. y)"
      using iso
      by (subst compose_id_inv_into, auto simp add:iso_def hom_def bij_betw_def)
    also have "\<dots> = x"
      using 3
      by (auto intro:compose_Id simp add:homr_def)
    finally
    show ?case .
  next
  case (4 y)
    hence "compose (carrier G1) (compose (carrier G2) y ?i') i
          = compose (carrier G1) y (compose (carrier G1) ?i' i)"
      using iso iso'
      by (auto intro: compose_assoc[THEN sym] simp add:iso_def hom_def homr_def)
    also have "\<dots> = compose (carrier G1) y (\<lambda>x\<in>carrier G1. x)"
      using iso
      by (subst compose_inv_into_id, auto simp add:iso_def hom_def bij_betw_def)
    also have "\<dots> = y"
      using 4
      by (auto intro:compose_Id simp add:homr_def)
    finally
    show ?case .
  qed
qed

theorem isomorphic_free_groups_bases_finite:
  assumes iso: "i \<in> \<F>\<^bsub>X\<^esub> \<cong> \<F>\<^bsub>Y\<^esub>"
      and finite: "finite X"
  shows "\<exists>f. bij_betw f X Y"
proof-
  obtain f
    where "bij_betw f (homr \<F>\<^bsub>Y\<^esub> C2) (homr \<F>\<^bsub>X\<^esub> C2)"
    using group_iso_betw_hom[OF free_group_is_group free_group_is_group iso]
    by auto
  moreover
  obtain g'
    where "bij_betw g' (Pow X) (homr (\<F>\<^bsub>X\<^esub>) C2)"
    using hom_F_C2_Powerset by auto
  then obtain g
    where "bij_betw g (homr (\<F>\<^bsub>X\<^esub>) C2) (Pow X)"
    by (auto intro: bij_betw_inv_into)
  moreover
  obtain h
    where "bij_betw h (Pow Y) (homr (\<F>\<^bsub>Y\<^esub>) C2)"
    using hom_F_C2_Powerset by auto
  ultimately
  have "bij_betw (g \<circ> f \<circ> h) (Pow Y) (Pow X)"
    by (auto intro: bij_betw_trans)
  hence eq_card: "card (Pow Y) = card (Pow X)"
    by (rule bij_betw_same_card)
  with finite
  have "finite (Pow Y)"
   by -(rule card_ge_0_finite, auto simp add:card_Pow)
  hence finite': "finite Y" by simp

  with eq_card finite
  have "card X = card Y"
   by (auto simp add:card_Pow)
  with finite finite'
  show ?thesis
   by (rule finite_same_card_bij)
qed

end