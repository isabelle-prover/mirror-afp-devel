(*  Title:       Executable Transitive Closures of Finite Relations
    Author:      Christian Sternagel <c.sternagel@gmail.com>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)

section \<open>Accessing Values via Keys\<close>

theory RBT_Map_Set_Extension
imports
  "HOL-Library.RBT"
  Matrix.Utility
begin
 
text \<open>
  We provide two extensions of the red black tree implementation.

  The first extension provides two convenience methods on sets which are represented by red black
  trees: a check on subsets and the big union operator. 

  The second extension is to provide two operations @{term elem_list_to_rm} and @{term
  rm_set_lookup} which can be used to index a set of values via keys. More precisely, given a list
  of values of type @{typ "'v"} and a key function of type @{typ "'v => 'k"}, @{term
  elem_list_to_rm} will generate a map of type @{typ "'k => 'v set"}. Then with @{term
  rs_set_lookup} we can efficiently access all values which match a given key.
\<close>

subsection \<open>Subset and Union\<close>

text \<open>For the subset operation @{term "r \<subseteq> s"} we provide an implementation
  that generates
  sorted lists for both @{term r} and @{term s} and then linearly checks the subset condition.\<close>

text \<open>
  As union operator we use the standard fold function. Note that the order of the union is important
  so that new sets are added to the big union.
\<close>

definition RBT_is_key where "RBT_is_key a t = (RBT.lookup t a \<noteq> None)" 
definition RBT_from_list where "RBT_from_list as = RBT.bulkload (map (\<lambda> x. (x,())) as)" 
definition RBT_list_union where "RBT_list_union as bs = RBT.union bs (RBT_from_list as)" 
definition RBT_keys where "RBT_keys t = dom (RBT.lookup t)" 

lemma set_RBT_keys: "set (RBT.keys t) = RBT_keys t" 
  unfolding RBT_keys_def by (simp add: lookup_keys)

lemma RBT_from_list[simp]: "RBT_keys (RBT_from_list xs) = set xs" 
  "set (RBT.keys (RBT_from_list xs)) = set xs" 
proof -
  have "x \<in> set xs \<Longrightarrow> map_of (map (\<lambda>x. (x, ())) xs) x = Some ()" for x
    by (induct xs, auto)
  thus "RBT_keys (RBT_from_list xs) = set xs" unfolding lookup_union lookup_bulkload RBT_from_list_def RBT_keys_def
    by (auto dest: map_of_SomeD)
  thus "set (RBT.keys (RBT_from_list xs)) = set xs" by (simp add: set_RBT_keys)
qed

lemmas RBT_defs = RBT_is_key_def RBT_list_union_def RBT_keys_def

definition rs_subset :: "('a :: linorder,unit) RBT.rbt \<Rightarrow> ('a,unit) RBT.rbt \<Rightarrow> 'a option"
where
  "rs_subset as bs = sorted_list_subset (RBT.keys as) (RBT.keys bs)"

lemma rs_subset [simp]:
  "rs_subset as bs = None \<longleftrightarrow> RBT_keys as \<subseteq> RBT_keys bs"
  unfolding rs_subset_def
  apply (subst sorted_list_subset[OF RBT.sorted_keys RBT.sorted_keys]) 
  apply (unfold RBT_keys_def lookup_keys[symmetric])
  by auto
  
definition rs_Union :: "('q :: linorder, unit) RBT.rbt list \<Rightarrow> ('q,unit) RBT.rbt"
where
  "rs_Union = foldl RBT.union (RBT.empty)"

lemma rs_Union [simp]:
  "RBT_keys (rs_Union qs) = \<Union> (RBT_keys ` set qs)"
proof -
  { 
    fix start
    have "RBT_keys (foldl RBT.union start qs) = RBT_keys start \<union> \<Union> (RBT_keys ` set qs)"
      unfolding RBT_keys_def
      by (induct qs arbitrary: start, auto simp: RBT.lookup_union)
  } from this[of "RBT.empty"]
  show ?thesis unfolding rs_Union_def
    unfolding RBT_keys_def
    by auto
qed

subsection \<open>Grouping Values via Keys\<close>
 
text \<open>
  The functions to produce the index (@{term elem_list_to_rm}) and the lookup function (@{term
  rm_set_lookup}) are straight-forward, however it requires some tedious reasoning that they perform
  as they should.
\<close>
fun elem_list_to_rm :: "('d \<Rightarrow> 'k :: linorder) \<Rightarrow> 'd list \<Rightarrow> ('k, 'd list) RBT.rbt "
where
  "elem_list_to_rm key [] = RBT.empty" |
  "elem_list_to_rm key (d # ds) =
    (let
      t = elem_list_to_rm key ds;
      k = key d
    in
      (case RBT.lookup t k of
        None \<Rightarrow> RBT.insert k [d] t
      | Some data \<Rightarrow> RBT.insert k (d # data) t))"

definition "rm_set_lookup rm = (\<lambda> a. (case RBT.lookup rm a of None \<Rightarrow> [] | Some rules \<Rightarrow> rules))"

locale rm_set = 
  fixes rm :: "('k :: linorder, 'd list) RBT.rbt"
    and key :: "'d \<Rightarrow> 'k"
    and data :: "'d set"
  assumes rm_set_lookup: "\<And> k. set (rm_set_lookup rm k) = {d \<in> data. key d = k}"
begin

lemma data_lookup:
  "data = \<Union> {set (rm_set_lookup rm k) | k. True}" (is "_ = ?R")
proof -
  { 
    fix d
    assume d: "d \<in> data"
    then have d: "d \<in> {d' \<in> data. key d' = key d}" by auto
    have "d \<in> ?R"
      by (rule UnionI[OF _ d], rule CollectI, rule exI[of _ "key d"], unfold rm_set_lookup[of "key d"], simp)
  }
  moreover
  {
    fix d
    assume "d \<in> ?R"
    from this[unfolded rm_set_lookup]
    have "d \<in> data" by auto
  }
  ultimately show ?thesis by blast
qed

lemma finite_data:
  "finite data"
  unfolding data_lookup
proof
  show "finite {set (rm_set_lookup rm k) | k. True}" (is "finite ?L")
  proof - 
    let ?rmset = "RBT.lookup rm"
    let ?M = "?rmset ` Map.dom ?rmset"
    let ?N = "((\<lambda> e. set (case e of None \<Rightarrow> [] | Some ds \<Rightarrow> ds)) ` ?M)"
    let ?K = "?N \<union> {{}}"
    have fin: "finite ?K" by auto 
    show ?thesis 
    proof (rule finite_subset[OF _ fin], rule)
      fix ds
      assume "ds \<in> ?L"
      from this[unfolded rm_set_lookup_def]
      obtain fn where ds: "ds = set (case RBT.lookup rm fn of None \<Rightarrow> []
          | Some ds \<Rightarrow> ds)" by auto
      show "ds \<in> ?K" 
      proof (cases "RBT.lookup rm fn")
        case None
        then show ?thesis unfolding ds by auto
      next
        case (Some rules)
        from Some have fn: "fn \<in> Map.dom ?rmset" by auto
        have "ds \<in> ?N"
          unfolding ds
          by (rule, rule refl, rule, rule refl, rule fn)
        then show ?thesis by auto
      qed
    qed
  qed
qed (force simp: rm_set_lookup_def)

end

interpretation elem_list_to_rm: rm_set "elem_list_to_rm key ds" key "set ds"
proof
  fix k
  show "set (rm_set_lookup (elem_list_to_rm key ds) k) = {d \<in> set ds. key d = k}"
  proof (induct ds arbitrary: k)
    case Nil
    then show ?case unfolding rm_set_lookup_def 
      by simp
  next
    case (Cons d ds k)
    let ?el = "elem_list_to_rm key"
    let ?l = "\<lambda>k ds. set (rm_set_lookup (?el ds) k)"
    let ?r = "\<lambda>k ds. {d \<in> set ds. key d = k}"
    from Cons have ind:
      "\<And> k. ?l k ds = ?r k ds" by auto
    show "?l k (d # ds) = ?r k (d # ds)"
    proof (cases "RBT.lookup (?el ds) (key d)")
      case None
      from None ind[of "key d"] have r: "{da \<in> set ds. key da = key d} = {}"
        unfolding rm_set_lookup_def by auto
      from None have el: "?el (d # ds) = RBT.insert (key d) [d] (?el ds)"
        by simp
      from None have ndom: "key d \<notin> Map.dom (RBT.lookup (?el ds))" by auto
      have r: "?r k (d # ds) = ?r k ds \<inter> {da. key da \<noteq> key d} \<union> {da . key da = k \<and> da = d}" (is "_ = ?r1 \<union> ?r2") using r by auto
      from ndom have l: "?l k (d # ds) = 
        set (case ((RBT.lookup (elem_list_to_rm key ds))(key d \<mapsto> [d])) k of None \<Rightarrow> []
        | Some rules \<Rightarrow> rules)" (is "_ = ?l") unfolding el rm_set_lookup_def 
        by simp
      {
        fix da
        assume "da \<in> ?r1 \<union> ?r2"
        then have "da \<in> ?l"
        proof
          assume "da \<in> ?r2"
          then have da: "da = d" and k: "key d = k" by auto
          show ?thesis unfolding da k by auto
        next
          assume "da \<in> ?r1"
          from this[unfolded ind[symmetric] rm_set_lookup_def]
          obtain das where rm: "RBT.lookup (?el ds) k = Some das" and da: "da \<in> set das" and k: "key da \<noteq> key d" 
            by (cases "RBT.lookup (?el ds) k", auto)
          from ind[of k, unfolded rm_set_lookup_def] rm da k have k: "key d \<noteq> k" by auto
          have rm: "((RBT.lookup (elem_list_to_rm key ds))(key d \<mapsto> [d])) k = Some das"
            unfolding rm[symmetric] using k by auto
          show ?thesis unfolding rm using da by auto
        qed
      } 
      moreover 
      {
        fix da
        assume l: "da \<in> ?l"
        let ?rm = "((RBT.lookup (elem_list_to_rm key ds))(key d \<mapsto> [d])) k"
        from l obtain das where rm: "?rm = Some das" and da: "da \<in> set das"
          by (cases ?rm, auto)
        have "da \<in> ?r1 \<union> ?r2" 
        proof (cases "k = key d")
          case True
          with rm da have da: "da = d" by auto
          then show ?thesis using True by auto
        next
          case False
          with rm have "RBT.lookup (?el ds) k = Some das" by auto
          from ind[of k, unfolded rm_set_lookup_def this] da False
          show ?thesis by auto
        qed
      }
      ultimately have "?l = ?r1 \<union> ?r2" by blast
      then show ?thesis unfolding l r .
    next
      case (Some das)
      from Some ind[of "key d"] have das: "{da \<in> set ds. key da = key d} = set das"
        unfolding rm_set_lookup_def by auto
      from Some have el: "?el (d # ds) = RBT.insert (key d) (d # das) (?el ds)"
        by simp
      from Some have dom: "key d \<in> Map.dom (RBT.lookup (?el ds))" by auto
      from dom have l: "?l k (d # ds) = 
        set (case ((RBT.lookup (elem_list_to_rm key ds))(key d \<mapsto> (d # das))) k of None \<Rightarrow> []
        | Some rules \<Rightarrow> rules)" (is "_ = ?l") unfolding el rm_set_lookup_def 
        by simp
      have r: "?r k (d # ds) = ?r k ds \<union> {da. key da = k \<and> da = d}" (is "_ = ?r1 \<union> ?r2")  by auto
      {
        fix da
        assume "da \<in> ?r1 \<union> ?r2"
        then have "da \<in> ?l"
        proof
          assume "da \<in> ?r2"
          then have da: "da = d" and k: "key d = k" by auto
          show ?thesis unfolding da k by auto
        next
          assume "da \<in> ?r1"
          from this[unfolded ind[symmetric] rm_set_lookup_def]
          obtain das' where rm: "RBT.lookup (?el ds) k = Some das'" and da: "da \<in> set das'" by (cases "RBT.lookup (?el ds) k", auto)
          from ind[of k, unfolded rm_set_lookup_def rm] have das': "set das' = {d \<in> set ds. key d = k}" by auto
          show ?thesis 
          proof (cases "k = key d")
            case True
            show ?thesis using das' das da unfolding True by simp
          next
            case False
            then show ?thesis using das' da rm by auto
          qed
        qed
      } 
      moreover 
      {
        fix da
        assume l: "da \<in> ?l"
        let ?rm = "((RBT.lookup (elem_list_to_rm key ds))(key d \<mapsto> d # das)) k"
        from l obtain das' where rm: "?rm = Some das'" and da: "da \<in> set das'"
          by (cases ?rm, auto)
        have "da \<in> ?r1 \<union> ?r2" 
        proof (cases "k = key d")
          case True
          with rm da das have da: "da \<in> set (d # das)" by auto
          then have "da = d \<or> da \<in> set das" by auto
          then have k: "key da = k" 
          proof
            assume "da = d"
            then show ?thesis using True by simp
          next
            assume "da \<in> set das"
            with das True show ?thesis by auto
          qed
          from da k show ?thesis using das by auto
        next
          case False
          with rm have "RBT.lookup (?el ds) k = Some das'" by auto
          from ind[of k, unfolded rm_set_lookup_def this] da False
          show ?thesis by auto
        qed
      }
      ultimately have "?l = ?r1 \<union> ?r2" by blast
      then show ?thesis unfolding l r .
    qed
  qed
qed

end
