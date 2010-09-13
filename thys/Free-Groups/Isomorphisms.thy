header {* Isomorphisms of Free Groups *}

theory "Isomorphisms"
imports
   "UnitGroup"
   "~~/src/HOL/Algebra/IntRing"
   "FreeGroups"
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
  have "f ` {()} \<subseteq> carrier int_group"
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

text {* Free Groups are isomorphic if their set of generators are isomorphic. The
converse holds as well, but is not shown here. That result could be achieved by
showing that it holds for free abelian groups @{text "\<int>\<^bsup>gens\<^esup>"},
which are the abelianization of Free Groups. *}

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
  proof(rule set_eqI,rule iffI)
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

end