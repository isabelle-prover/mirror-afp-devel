header {* The Nielsen-Schreier theorem *}

theory "NielsenSchreier"
imports
   "FreeGroups"
   "~~/src/HOL/Algebra/Coset"
begin

text {*
The Nielsen-Schreier theorem states that subgroups of Free Groups are free. Nice
and short proofs exists using Topology and are not available here at the moment.
Therefore, we have to stick to longer but elementary proofs.

We follow \cite{rotmam}, section 4.6.
*}

section {* Traversals *}

text {*
A traversal for a subgroup of a group is a choice of representatives per
coset, where the subgroup is represented by the empty word.
*}

locale traversal = group +
  fixes H and l
  assumes is_subgroup: "H \<le> G"
      and is_traversal: "\<forall> c \<in> rcosets H. l c \<in> c"
      and empty_on_H: "p H = \<one>"

lemma (in traversal) l_closed [simp, intro]:
  assumes "b \<in> carrier G"
  shows "l (H #> b) \<in> carrier G"
proof-
  have "H #> b \<in> rcosets H"
    by(rule rcosetsI[OF subgroup.subset[OF is_subgroup] assms])
  hence "l (H #> b) \<in> (H #> b)" by (auto simp add: is_traversal)
  also have "\<dots> \<subseteq> carrier G"
    by(rule r_coset_subset_G[OF subgroup.subset[OF is_subgroup] assms])
  finally show ?thesis .
qed

text {*
For sake of a better name, we call this traversed, because it is an element
obtained by traversing the coset graph.
*}

definition (in traversal)
  traversed
  where "traversed b v = l (H #> b) \<otimes> v \<otimes> inv (l (H #> (b \<otimes> v)))"

lemma (in traversal) traversed_closed [simp,intro]:
  "\<lbrakk> b \<in> carrier G ; v \<in> carrier G \<rbrakk> \<Longrightarrow> traversed b v \<in> carrier G"
unfolding traversed_def by auto

lemma (in traversal) traversed_inv [simp,intro]:
  "\<lbrakk> b \<in> carrier G ; v \<in> carrier G \<rbrakk> \<Longrightarrow>
   inv (traversed b v) = traversed (b \<otimes> v) (inv v)"
unfolding traversed_def
by (auto simp add: inv_mult_group m_assoc)

locale freegroup = fixes gens :: "'a set" and F (structure)
  defines F_def[simp]: "F \<equiv> free_group gens" 
  
sublocale freegroup < group "free_group gens"
  by (rule free_group_is_group)

locale free_traversal = freegroup + traversal "free_group gens"

text {*
For each coset, we define a coset function. These need to be defined
simultaniously.
*}

fun (in free_traversal) coset_fun :: "_ \<Rightarrow> _ \<Rightarrow> _"   ("_ \<^bsup>_\<^esup>")
  where "[]\<^bsup>b\<^esup> = \<one>"
      | "(t#v)\<^bsup>b\<^esup> = (
            case t of (False, g) \<Rightarrow>      traversed  b              (\<iota> g)
                    | (True, g)  \<Rightarrow> inv (traversed (b \<otimes> inv (\<iota> g)) (\<iota> g))
            ) \<otimes> (v \<^bsup>b \<otimes> [t]\<^esup>)"

lemma (in free_traversal) coset_fun_id[simp]:
  "\<one> \<^bsup>b\<^esup> = \<one>"
  by (auto simp add:free_group_def)

declare (in free_traversal) coset_fun_id[unfolded F_def, simp]

lemma generator_singletonD:
  "t#l \<in> carrier (free_group gens) \<Longrightarrow> snd t \<in> gens"
  by (simp add: free_group_def occuring_generators_def)

lemma canceled_appendD:
  assumes "canceled (a @ b)"
  shows "canceled a" and "canceled b"
proof-
  show "canceled a"
  proof(rule ccontr)
    assume "\<not> canceled a"
    hence "DomainP cancels_to_1 a" by (simp add: canceled_def)
    then obtain a' where "cancels_to_1 a a'" by auto
    then obtain i where "cancels_to_1_at i a a'" by (auto simp add:cancels_to_1_def)
    hence "Suc i < length a" and "canceling (a ! i) (a ! Suc i)"
      by (auto simp add:cancels_to_1_at_def)
    hence "canceling ((a @ b) ! i) ((a @ b) ! Suc i)" 
      by (auto simp add:nth_append)
    hence "cancels_to_1_at i (a@b) (cancel_at i (a@b))" using `Suc i < length a`
      by (auto simp add:cancels_to_1_at_def)
    hence "cancels_to_1 (a@b) (cancel_at i (a@b))" by (auto simp add:cancels_to_1_def)
    hence "\<not> canceled (a @ b)" by (auto simp add:canceled_def)
    thus False using `canceled (a@b)` by auto
  qed
  show "canceled b"
  proof(rule ccontr)
    assume "\<not> canceled b"
    hence "DomainP cancels_to_1 b" by (simp add: canceled_def)
    then obtain b' where "cancels_to_1 b b'" by auto
    then obtain i where "cancels_to_1_at i b b'" by (auto simp add:cancels_to_1_def)
    hence "Suc i < length b" and "canceling (b ! i) (b ! Suc i)"
      by (auto simp add:cancels_to_1_at_def)
    hence "canceling ((a @ b) ! (length a + i)) ((a @ b) ! (length a + Suc i))"
      by (auto simp add:nth_append)
    hence "cancels_to_1_at (length a + i) (a@b) (cancel_at (length a + i) (a@b))" using `Suc i < length b`
      by (auto simp add:cancels_to_1_at_def)
    hence "cancels_to_1 (a@b) (cancel_at (length a + i) (a@b))" by (auto simp add:cancels_to_1_def)
    hence "\<not> canceled (a @ b)" by (auto simp add:canceled_def)
    thus False using `canceled (a@b)` by auto
  qed
qed


lemma carrier_appendD:
 assumes "a @ b \<in> carrier (free_group gens)"
 shows "a \<in> carrier (free_group gens)" and  "b \<in> carrier (free_group gens)"
  using assms
  by(auto simp add: free_group_def occuring_generators_def dest:canceled_appendD)

lemma (in free_traversal) coset_fun_closed [simp,intro]:
  "\<lbrakk> u \<in> carrier F ; b \<in> carrier F \<rbrakk> \<Longrightarrow> u\<^bsup>b\<^esup> \<in> carrier F"
proof(induct u b rule: coset_fun.induct)
print_cases 
  case 1 show ?case by simp
next
  case (2 t b v)
    from `t # b \<in> carrier F` have "[t] @ b \<in> carrier F" by simp
    hence "[t] \<in> carrier F" and "b \<in> carrier F"
      unfolding F_def by (rule carrier_appendD)+
    with 2 have "b \<^bsup>v \<otimes> [t]\<^esup> \<in> carrier F" by auto
    thus ?case using `[t] \<in> carrier F` and `v \<in> carrier F`
      by (auto intro!: m_closed traversed_closed insert_closed inv_closed
             simp add:prod_case_unfold split:bool.split
             dest: generator_singletonD)
qed

declare (in free_traversal) coset_fun_closed[unfolded F_def, simp, intro]


lemma canceled_cons:
  "\<lbrakk>\<not> canceling y x; canceled (x # v')\<rbrakk> \<Longrightarrow> canceled (y # x # v')"
proof(rule ccontr)
  assume "\<not>  canceled (y # x # v')"
  then obtain i where c: "canceling ((y # x # v') ! i) ((y # x # v') ! Suc i)"
     and l:  "Suc i < length (y#x#v')"
    by (auto simp add: canceled_def cancels_to_1_def cancels_to_1_at_def)
  moreover assume "\<not> canceling y x"
  ultimately obtain j where "i = Suc j" and l': "Suc j < length (x#v')"
    using l by (cases i, auto)
  with c have "canceling ((x # v') ! j) ((x # v') ! Suc j)" by auto
  with l' and Cons have "cancels_to_1 (x # v') (cancel_at j (x# v'))"
    by (auto simp add: cancels_to_1_def cancels_to_1_at_def)
  moreover assume "canceled (x # v')"
  ultimately show False by (auto simp add:canceled_def)
qed

lemma (in freegroup) mult_singleton:
  "\<lbrakk>\<not> canceling y x; x # v' \<in> carrier F \<rbrakk> \<Longrightarrow> [y] \<otimes> (x#v') = y#x#v'"
  by (auto simp add:free_group_def intro!: normalize_idemp canceled_cons)

lemma (in freegroup) free_group_mult_induct[consumes 2, case_names empty_r empty_l cancel non_cancel append]:
  assumes carr_u: "u \<in> carrier F"
      and carr_v: "v \<in> carrier F"
      and empty_r: "\<And> u. u \<in> carrier F \<Longrightarrow> P u \<one>"
      and empty_l: "\<And> v. v \<in> carrier F \<Longrightarrow> P \<one> v"
      and cancel: "\<And> v x.
          \<lbrakk> [x] \<in> carrier F
          ; (x#v) \<in> carrier F
          \<rbrakk> \<Longrightarrow> P (inv [x]) (x#v)"
      and non_cancel: "\<And> v x y.
          \<lbrakk> \<not> canceling y x
          ; [y] \<otimes> (x#v) = y#x#v
          ; [y] \<in> carrier F
          \<rbrakk> \<Longrightarrow> P [y] (x#v)"
      and append: "\<And> u v x y.
          \<lbrakk> P (y#u) v
          ; (x#y#u) \<otimes> v = x # (y#u)\<otimes>v
          ; x#y#u \<in> carrier F
          ; v \<in> carrier F
          (*; (x#y#u) \<otimes> v = x # (u \<otimes> v) *)
          \<rbrakk> \<Longrightarrow> P (x#y#u) v"
  shows "P u v"
using carr_u and carr_v
proof(induct u arbitrary: v)
case Nil show ?case using empty_l and `v \<in> carrier F`
  by (auto simp add: free_group_def) next
case (Cons y u')
  have "[y] \<in> carrier F" and "u' \<in> carrier F"  using `y#u' \<in> carrier F`
    by (auto intro: carrier_appendD(1)[of _ u'] carrier_appendD(2)[of "[y]"])
  show ?case
  proof (cases u')
  case Nil show ?thesis
    proof (cases v)
      case Nil thus ?thesis using `y#u' \<in> carrier F` and empty_r
        by (auto simp add: free_group_def) next
      case (Cons x v')
        have "[x] \<in> carrier F" using `v = x#v'` and `v \<in> carrier F`
          by (auto intro: carrier_appendD(1)[of _ v'])
        from Cons show ?thesis
        proof (cases "canceling y x" )
          case True
          hence "canceling x y" by (rule cancel_sym)
          hence "[y] = inv [x]" using `[x]\<in> carrier F`
            by(cases x, simp add: canceling_def inv_fg_def inv1_def)
          thus ?thesis
            using Nil Cons cancel `[x] \<in> carrier F` `v \<in> carrier F`
            by auto
        next
          case False with `v \<in> carrier F` `[y] \<in> carrier F` Cons
          have "[y] \<otimes> (x#v') = y#x#v'"
            by (auto dest!: mult_singleton) 
          with False show ?thesis using Nil Cons non_cancel `[y] \<in> carrier F` by auto
        qed
    qed
  next
    fix y' u''
    assume "u' = y' # u''"
    have "P u' v"
      by (rule Cons.hyps[OF `u' \<in> carrier F` `v \<in> carrier F`])
    moreover 
    have "(y # y' # u'') \<otimes> v = y # (y' # u'') \<otimes> v"
      using `y#u' \<in> carrier F`  `u' = y' # u''` 
      thm canceled_cons
      apply (auto simp add:free_group_def intro!: normalize_idemp)
      sorry
      
    ultimately show ?thesis
    using `y#u' \<in> carrier F` and `v \<in> carrier F`
      by (auto intro!: append simp: `u' = y' # u''`)
  qed
qed


lemma (in freegroup) inv_cons[simp]:
  assumes "[x] \<in> carrier F" and "v \<in> carrier F"
  shows "inv [x] \<otimes> (x # v) = v"
proof-
  have "cancels_to_1_at 0 (inv1 x # x # v) v"
    by(simp add: cancels_to_1_at_def cancel_at_def canceling_def inv1_def)
  hence "cancels_to_1 (inv1 x # x # v) v" by (auto simp add: cancels_to_1_def)
  hence "cancels_to (inv1 x # x # v) v" by (simp add: cancels_to_def)
  hence "normalize (inv1 x # x # v) = normalize v" by (rule normalize_canceled)
  thus ?thesis using assms
    by (simp add: inv_fg_def, simp add:free_group_def)
qed

lemma (in free_traversal) lemma4_89_1:
  assumes "u \<in> carrier F" and "v \<in> carrier F" and "b \<in> carrier F"
  shows "(u \<otimes> v)\<^bsup>b\<^esup> = u\<^bsup>b\<^esup> \<otimes> (v\<^bsup>b \<otimes> u\<^esup>)"
using assms
proof(induct  arbitrary: b rule: free_group_mult_induct)
case (empty_r u) thus ?case using `b \<in> carrier F` by auto next
case (empty_l u) thus ?case using `b \<in> carrier F` by auto next
case (cancel v x)
  hence "v \<in> carrier F"
    by (auto simp add: F_def intro: carrier_appendD(2)[of "[x]"])
  from inv_cons[OF `[x] \<in> carrier F` `v \<in> carrier F`]
  have "(inv [x] \<otimes> (x # v)) \<^bsup>b\<^esup> = v \<^bsup>b\<^esup>" by simp
  also
  have "\<dots> = inv (traversed (b \<otimes> inv [x]) [x]) \<otimes>
             (traversed (b \<otimes> inv [x]) [x] \<otimes> (v \<^bsup>b\<^esup>))"
  proof-
    have "traversed (b \<otimes> inv [x]) [x] \<in> carrier F"
      using `[x] \<in> carrier F` `b \<in> carrier F` by (auto simp del: inv_is_inv_fg)
    thus ?thesis using `v \<in> carrier F` `b \<in> carrier F`
    by (auto simp add: m_assoc[THEN sym] simp del: inv_is_inv_fg)
  qed
  also have "\<dots> =
    (inv [x])\<^bsup> b \<^esup> \<otimes>
    ((x # v)\<^bsup> (b \<otimes> inv [x]) \<^esup>)" (is "?lhs1 \<otimes> ?lhs2 = ?rhs1 \<otimes> ?rhs2")
  proof-
    have "?lhs2 = ?rhs2"
    proof (cases "fst x")
      case False
      thus ?thesis using `[x] \<in> carrier F` and `v \<in> carrier F` and `b \<in> carrier F`
        by (cases x, auto split:bool.split simp add: insert_def m_assoc simp del: inv_is_inv_fg)
    next
      case True
      hence "[(False,snd x)] \<in> carrier F" using `[x] \<in> carrier F`
        by (auto simp add:inv_fg_def free_group_def inv1_def occuring_generators_def)
      with True
      show ?thesis using `[x] \<in> carrier F` and `v \<in> carrier F` and `b \<in> carrier F`
        apply (cases x)
        apply (auto split:bool.split simp add: insert_def m_assoc simp del: inv_is_inv_fg)         
        apply (simp add:inv_is_inv_fg inv_fg_def inv1_def)
        done
    qed
    moreover
    have "?lhs1 = ?rhs1"
      proof (cases "fst x")
      case False
        hence "inv [x] = [(True, snd x)]" using  `[x] \<in> carrier F`
          by (cases x, auto simp add: inv_fg_def inv1_def)
        moreover have "[(True,snd x)] \<in> carrier F" using `[x] \<in> carrier F`
        by (auto simp add:inv_fg_def free_group_def inv1_def occuring_generators_def)
        ultimately
        show ?thesis using False `[x] \<in> carrier F` `b \<in> carrier F`
          by(cases x, auto simp del: inv_is_inv_fg  simp add: insert_def) 
      next
      case True
        hence "inv [x] = [(False, snd x)]" using  `[x] \<in> carrier F`
          by (cases x, auto simp add: inv_fg_def inv1_def)
        moreover have "[(False,snd x)] \<in> carrier F" using `[x] \<in> carrier F`
        by (auto simp add:inv_fg_def free_group_def inv1_def occuring_generators_def)
        moreover have "[(False, snd x)] \<otimes> [(True, snd x)] = \<one>"
        proof-
          have "inv [x] \<otimes> [x] = \<one>" using `[x] \<in> carrier F`
            by (auto simp del : inv_is_inv_fg)
          thus ?thesis using True using `[x] \<in> carrier F`
            by  (cases x, auto simp add: inv_fg_def inv1_def)
        qed
        ultimately
        show ?thesis using True `[x] \<in> carrier F` `b \<in> carrier F`
          by (cases x, auto simp del: inv_is_inv_fg  simp add: m_assoc insert_def) 
      qed
    ultimately
    show ?thesis by simp
  qed
  finally
  show ?case . 
next
  case (non_cancel v x y)
  hence "([y] \<otimes> (x # v)) \<^bsup>b\<^esup> = (y # x # v) \<^bsup>b\<^esup>"
    by auto
  also have "\<dots> = (
            case y of (False, g) \<Rightarrow>      traversed  b              (\<iota> g)
                    | (True, g)  \<Rightarrow> inv (traversed (b \<otimes> inv (\<iota> g)) (\<iota> g))
            ) \<otimes> ((x#v) \<^bsup>b \<otimes> [y]\<^esup>)" by simp
  also have "\<dots> = [y] \<^bsup>b\<^esup> \<otimes> ((x#v) \<^bsup>b \<otimes> [y]\<^esup>)"
            (is "?lhs1 \<otimes> ?lhs2 = ?rhs1 \<otimes> ?rhs2")
  proof-
    have "[(False,snd y)] \<in> carrier F" using `[y] \<in> carrier F`
      by (auto simp add:inv_fg_def free_group_def inv1_def occuring_generators_def)
    hence "?lhs1 = ?rhs1" using `[y] \<in> carrier F` `b \<in> carrier F`
      by (cases y, auto split:bool.split simp add: insert_def simp del: inv_is_inv_fg )
    thus ?thesis by simp
  qed
  finally show ?case .
next
print_cases
  case (append u v x y)
  hence "[x] \<in> carrier F" and "y#u \<in> carrier F" using  `x # y # u \<in> carrier F`
    by (auto dest:carrier_appendD[of "[x]", simplified])
  from  `[x] \<in> carrier F`
  have "inv [x] \<in> carrier F" by (auto simp del:inv_is_inv_fg)
  from append(2)
  have "((x # y # u) \<otimes> v) \<^bsup>b\<^esup> = (x # (y # u) \<otimes> v) \<^bsup>b\<^esup>" by simp
  also have "\<dots> =  (
            case x of (False, g) \<Rightarrow>      traversed  b              (\<iota> g)
                    | (True, g)  \<Rightarrow> inv (traversed (b \<otimes> inv (\<iota> g)) (\<iota> g))
            ) \<otimes> (((y # u) \<otimes> v) \<^bsup>b \<otimes> [x]\<^esup>)"
  by simp
  also have "\<dots> = (
            case x of (False, g) \<Rightarrow>      traversed  b              (\<iota> g)
                    | (True, g)  \<Rightarrow> inv (traversed (b \<otimes> inv (\<iota> g)) (\<iota> g))
            ) \<otimes> (((y # u) \<^bsup>b \<otimes> [x]\<^esup>) \<otimes> (v \<^bsup>b \<otimes> [x] \<otimes> (y # u)\<^esup>))"
    using `b \<in> carrier F` and `[x] \<in> carrier F`
    apply (subst append) by simp_all
  also have "\<dots> = (
            case x of (False, g) \<Rightarrow>      traversed  b              (\<iota> g)
                    | (True, g)  \<Rightarrow> inv (traversed (b \<otimes> inv (\<iota> g)) (\<iota> g))
            ) \<otimes> ((y # u) \<^bsup>b \<otimes> [x]\<^esup>) \<otimes> (v \<^bsup>b \<otimes> [x] \<otimes> (y # u)\<^esup>)"
         using `b \<in> carrier F` and `[x] \<in> carrier F` and `y#u \<in> carrier F` and `inv [x] \<in> carrier F` `v \<in> carrier F`
    apply (subst (2) m_assoc[folded F_def])
    apply (cases x)
    apply (auto simp add: insert_def inv_fg_def inv1_def simp del: coset_fun.simps split:bool.split
      intro!:inv_closed traversed_closed m_closed)
    done
  also have "\<dots> = ((x # y # u) \<^bsup>b\<^esup>) \<otimes> (v \<^bsup>b \<otimes> [x] \<otimes> (y # u)\<^esup>)"
    by simp
  also have "\<dots> = ((x # y # u) \<^bsup>b\<^esup>) \<otimes> (v \<^bsup>b \<otimes> (x # y # u)\<^esup>)"
    proof-
      have "[x] \<otimes> (y # u) = x # y # u" using `x # y # u \<in> carrier F`
        by (auto simp add:free_group_def)
      hence "b \<otimes> [x] \<otimes> (y # u) = b \<otimes> (x # y # u)"
        apply (subst m_assoc[folded F_def,
           OF `b \<in> carrier F` `[x]\<in> carrier F` `y # u \<in> carrier F`])
        apply simp
        done
      thus ?thesis by simp
    qed
  finally
  show ?case .
qed

end