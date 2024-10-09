section \<open>Computing Nonempty and Infinite sorts\<close>

text \<open>This theory provides two algorithms, which both take a description of a set of sorts with
  their constructors. The first algorithm computes the set of sorts that are nonempty, i.e., those
  sorts that are inhabited by ground terms; 
  and the second algorithm computes the set of sorts that are infinite,
  i.e., where one can build arbitrary large ground terms.\<close>

theory Compute_Nonempty_Infinite_Sorts
  imports 
    Sorted_Terms.Sorted_Terms
    LP_Duality.Minimum_Maximum
    Matrix.Utility
    FinFun.FinFun
begin

(* TODO: move to some library *)
lemma finite_set_Cons:
  assumes A: "finite A" and B: "finite B"
  shows "finite (set_Cons A B)" 
proof -
  have "set_Cons A B = case_prod (#) ` (A \<times> B)" by (auto simp: set_Cons_def)
  then show ?thesis
    by (simp add: finite_imageI[OF finite_cartesian_product[OF A B],of "case_prod (#)"])
qed

lemma finite_listset:
  assumes "\<forall>A \<in> set As. finite A"
  shows "finite (listset As)"
  using assms
  by (induct As) (auto simp: finite_set_Cons)
  
lemma listset_conv_nth:
  "xs \<in> listset As = (length xs = length As \<and> (\<forall>i < length As. xs ! i \<in> As ! i))"
proof (induct As arbitrary: xs)
  case (Cons A As xs) then show ?case
    by (cases xs) (auto simp: set_Cons_def nth_Cons nat.splits)
qed auto

lemma card_listset: assumes "\<And> A. A \<in> set As \<Longrightarrow> finite A" 
  shows "card (listset As) = prod_list (map card As)" 
  using assms
proof (induct As)
  case (Cons A As)
  have sC: "set_Cons A B = case_prod (#) ` (A \<times> B)" for B by (auto simp: set_Cons_def)
  have IH: "prod_list (map card As) = card (listset As)" using Cons by auto
  have "card A * card (listset As) = card (A \<times> listset As)"
    by (simp add: card_cartesian_product)
  also have "\<dots> = card ((\<lambda> (a,as). Cons a as) ` (A \<times> listset As))" 
    by (subst card_image, auto simp: inj_on_def)
  finally
  show ?case by (simp add: sC IH)
qed auto
(* end for library *)


subsection \<open>Deciding the nonemptyness of all sorts under consideration\<close>

function compute_nonempty_main :: "'\<tau> set \<Rightarrow> (('f \<times> '\<tau> list) \<times> '\<tau>) list \<Rightarrow> '\<tau> set" where
  "compute_nonempty_main ne ls = (let rem_ls = filter (\<lambda> f. snd f \<notin> ne) ls in
     case partition (\<lambda> ((_,args),_). set args \<subseteq> ne) rem_ls of
      (new, rem) \<Rightarrow> if new = [] then ne else compute_nonempty_main (ne \<union> set (map snd new)) rem)"
  by pat_completeness auto

termination
proof (relation "measure (length o snd)", goal_cases)
  case (2 ne ls rem_ls new rem)   
  have "length new + length rem = length rem_ls" 
    using 2(2) sum_length_filter_compl[of _ rem_ls] by (auto simp: o_def)
  with 2(3) have "length rem < length rem_ls" by (cases new, auto)
  also have "\<dots> \<le> length ls" using 2(1) by auto
  finally show ?case by simp
qed simp

declare compute_nonempty_main.simps[simp del]

definition compute_nonempty_sorts :: "(('f \<times> '\<tau> list) \<times> '\<tau>) list \<Rightarrow> '\<tau> set" where
  "compute_nonempty_sorts Cs = compute_nonempty_main {} Cs" 

lemma compute_nonempty_sorts:  
  assumes "distinct (map fst Cs)" (* no conflicting asssignments in list-representation *)
  and "map_of Cs = C" (* list-representation corresponds to function representation *)
shows "compute_nonempty_sorts Cs = {\<tau>. \<exists> t :: ('f,'v)term. t : \<tau> in \<T>(C,\<emptyset>)}" (is "_ = ?NE")
proof -
  let ?TC = "\<T>(C,(\<emptyset> :: 'v \<Rightarrow> _))" 
  have "ne \<subseteq> ?NE \<Longrightarrow> set ls \<subseteq> set Cs \<Longrightarrow> snd ` (set Cs - set ls) \<subseteq> ne \<Longrightarrow>
    compute_nonempty_main ne ls = ?NE" for ne ls
  proof (induct ne ls rule: compute_nonempty_main.induct)
    case (1 ne ls)
    note ne = 1(2)
    define rem_ls where "rem_ls = filter (\<lambda> f. snd f \<notin> ne) ls" 
    have rem_ls: "set rem_ls \<subseteq> set Cs"
       "snd ` (set Cs - set rem_ls) \<subseteq> ne" 
      using 1(2-) by (auto simp: rem_ls_def)
    obtain new rem where part: "partition (\<lambda>((f, args), target). set args \<subseteq> ne) rem_ls = (new,rem)" by force
    have [simp]: "compute_nonempty_main ne ls = (if new = [] then ne else compute_nonempty_main (ne \<union> set (map snd new)) rem)" 
      unfolding compute_nonempty_main.simps[of ne ls] Let_def rem_ls_def[symmetric] part by auto
    have new: "set (map snd new) \<subseteq> ?NE"
    proof
      fix \<tau>
      assume "\<tau> \<in> set (map snd new)" 
      then obtain f args where "((f,args),\<tau>) \<in> set rem_ls" and args: "set args \<subseteq> ne" using part by auto
      with rem_ls have "((f,args),\<tau>) \<in> set Cs" by auto
      with assms have "C (f,args) = Some \<tau>" by auto
      hence fC: "f : args \<rightarrow> \<tau> in C" by (simp add: fun_hastype_def)
      from args ne have "\<forall> tau. \<exists> t. tau \<in> set args \<longrightarrow> t : tau in ?TC" by auto
      from choice[OF this] obtain ts where "\<And> tau. tau \<in> set args \<Longrightarrow> ts tau : tau in ?TC" by auto
      hence "Fun f (map ts args) : \<tau> in ?TC" 
        apply (intro Fun_hastypeI[OF fC]) 
        by (simp add: list_all2_conv_all_nth)
      thus "\<tau> \<in> ?NE" by auto
    qed
    show ?case
    proof (cases "new = []")
      case False
      note IH = 1(1)[OF rem_ls_def part[symmetric] False]
      have "compute_nonempty_main ne ls = compute_nonempty_main (ne \<union> set (map snd new)) rem" using False by simp
      also have "\<dots> = ?NE" 
      proof (rule IH)
        show "ne \<union> set (map snd new) \<subseteq> ?NE" using new ne by auto
        show "set rem \<subseteq> set Cs" using rem_ls part by auto
        show "snd ` (set Cs - set rem) \<subseteq> ne \<union> set (map snd new)"
        proof
          fix \<tau>
          assume "\<tau> \<in> snd ` (set Cs - set rem)" 
          then obtain f args where in_ls: "((f,args),\<tau>) \<in> set Cs" and nrem: "((f,args),\<tau>) \<notin> set rem" by force
          thus "\<tau> \<in> ne \<union> set (map snd new)" using new part rem_ls by force (* takes a few seconds *)
        qed
      qed
      finally show ?thesis .
    next
      case True
      have "compute_nonempty_main ne ls = ne" using True by simp
      also have "\<dots> = ?NE" 
      proof (rule ccontr)
        assume "\<not> ?thesis" 
        with ne obtain \<tau> t where counter: "t : \<tau> in ?TC" "\<tau> \<notin> ne" by auto
        thus False 
        proof (induct t \<tau>)
          case (Fun f ts \<tau>s \<tau>)
          from Fun(1) have "C (f,\<tau>s) = Some \<tau>" by (simp add: fun_hastype_def)
          with assms(2) have mem: "((f,\<tau>s),\<tau>) \<in> set Cs" by (meson map_of_SomeD)
          from Fun(3) have \<tau>s: "set \<tau>s \<subseteq> ne" by (induct, auto)
          from rem_ls mem Fun(4) have "((f,\<tau>s),\<tau>) \<in> set rem_ls" by auto
          with \<tau>s have "((f,\<tau>s),\<tau>) \<in> set new" using part by auto
          with True show ?case by auto
        qed auto
      qed
      finally show ?thesis .
    qed
  qed
  from this[of "{}" Cs] show ?thesis unfolding compute_nonempty_sorts_def by auto
qed

definition decide_nonempty_sorts :: "'t list \<Rightarrow> (('f \<times> 't list) \<times> 't)list \<Rightarrow> 't option" where
  "decide_nonempty_sorts \<tau>s Cs = (let ne = compute_nonempty_sorts Cs in
   find (\<lambda> \<tau>. \<tau> \<notin> ne) \<tau>s)" 

lemma decide_nonempty_sorts:  
  assumes "distinct (map fst Cs)" (* no conflicting asssignments in list-representation *)
  and "map_of Cs = C" (* list-representation corresponds to function representation *)
shows "decide_nonempty_sorts \<tau>s Cs = None \<Longrightarrow> \<forall> \<tau> \<in> set \<tau>s. \<exists> t :: ('f,'v)term. t : \<tau> in \<T>(C,\<emptyset>)"
  "decide_nonempty_sorts \<tau>s Cs = Some \<tau> \<Longrightarrow> \<tau> \<in> set \<tau>s \<and> \<not> (\<exists> t :: ('f,'v)term. t : \<tau> in \<T>(C,\<emptyset>))" 
  unfolding decide_nonempty_sorts_def Let_def compute_nonempty_sorts[OF assms, where ?'v = 'v]
    find_None_iff find_Some_iff by auto


subsection \<open>Deciding infiniteness of a sort and computing cardinalities\<close>

text \<open>We provide an algorithm, that given a list of sorts with constructors, computes the
  set of those sorts that are infinite. Here a sort is defined as infinite iff 
   there is no upper bound on the size of the ground terms of that sort.
  Moreover, we also compute for each sort the cardinality of the set of constructor ground
  terms of that sort.\<close>

context
begin 

unbundle finfun_syntax  

fun finfun_update_all :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow>f 'b) \<Rightarrow> ('a \<Rightarrow>f 'b)" where
  "finfun_update_all [] g f = f" 
| "finfun_update_all (x # xs) g f = (finfun_update_all xs g f)(x $:= g x)"

lemma finfun_update_all[simp]: "finfun_update_all xs g f $ x = (if x \<in> set xs then g x else f $ x)"
proof (induct xs)
  case (Cons y xs)
  thus ?case by (cases "x = y", auto)
qed auto


definition compute_card_of_sort :: "'\<tau> \<Rightarrow> ('f \<times> '\<tau> list)list \<Rightarrow> ('\<tau> \<Rightarrow>f nat) \<Rightarrow> nat" where
  "compute_card_of_sort \<tau> cs cards = (\<Sum>f\<sigma>s\<leftarrow>remdups cs. prod_list (map (($) cards) (snd f\<sigma>s)))" 
 
(* second argument: take list of types combined with constructors *)
function compute_inf_card_main :: "'\<tau> set \<Rightarrow> ('\<tau> \<Rightarrow>f nat) \<Rightarrow> ('\<tau> \<times> ('f \<times> '\<tau> list)list) list \<Rightarrow> '\<tau> set \<times> ('\<tau> \<Rightarrow> nat)" where
  "compute_inf_card_main m_inf cards ls = (
   let (fin, ls') = 
         partition (\<lambda> (\<tau>,fs). \<forall> \<tau>s \<in> set (map snd fs). \<forall> \<tau> \<in> set \<tau>s. \<tau> \<notin> m_inf) ls 
    in if fin = [] then (m_inf, \<lambda> \<tau>. cards $ \<tau>) else 
      let new = map fst fin; 
       cards' = finfun_update_all new (\<lambda> \<tau>. compute_card_of_sort \<tau> (the (map_of ls \<tau>)) cards) cards in 
       compute_inf_card_main (m_inf - set new) cards' ls')" 
  by pat_completeness auto

termination
proof (relation "measure (length o snd o snd)", goal_cases)
  case (2 m_inf cards ls pair fin ls')   
  have "length fin + length ls' = length ls" 
    using 2 sum_length_filter_compl[of _ ls] by (auto simp: o_def)
  with 2(3) have "length ls' < length ls" by (cases fin, auto)
  thus ?case by auto
qed simp  

lemma compute_inf_card_main: fixes E :: "'v \<rightharpoonup> 't" and C :: "('f,'t)ssig"
  assumes E: "E = \<emptyset>" 
  and C_Cs: "C = map_of Cs'" 
  and Cs': "set Cs' = set (concat (map ((\<lambda> (\<tau>, fs). map (\<lambda> f. (f,\<tau>)) fs)) Cs))" 
  and arg_types_inhabitet: "\<forall> f \<tau>s \<tau> \<tau>'. f : \<tau>s \<rightarrow> \<tau> in C \<longrightarrow> \<tau>' \<in> set \<tau>s \<longrightarrow> (\<exists> t. t : \<tau>' in \<T>(C,E))" 
  and dist: "distinct (map fst Cs)" "distinct (map fst Cs')"
  and inhabitet: "\<forall> \<tau> fs. (\<tau>,fs) \<in> set Cs \<longrightarrow> set fs \<noteq> {}" 
  and "\<forall> \<tau>. \<tau> \<notin> m_inf \<longrightarrow> bdd_above (size ` {t. t : \<tau> in \<T>(C,E)})" 
  and "set ls \<subseteq> set Cs" 
  and "fst ` (set Cs - set ls) \<inter> m_inf = {}" 
  and "m_inf \<subseteq> fst ` set ls" 
  and "\<forall> \<tau>. \<tau> \<notin> m_inf \<longrightarrow> cards $ \<tau> = card {t. t : \<tau> in \<T>(C,E)} \<and> finite {t. t : \<tau> in \<T>(C,E)}" 
  and "\<forall> \<tau>. \<tau> \<in> m_inf \<longrightarrow> cards $ \<tau> = 0" 
shows "compute_inf_card_main m_inf cards ls = ({\<tau>. \<not> bdd_above (size ` {t. t : \<tau> in \<T>(C,E)})},
         \<lambda> \<tau>. card {t. t : \<tau> in \<T>(C,E)})" 
  using assms(8-)
proof (induct m_inf cards ls rule: compute_inf_card_main.induct)
  case (1 m_inf cards ls)
  let ?terms = "\<lambda> \<tau>. {t. t : \<tau> in \<T>(C,E)}" 
  let ?fin = "\<lambda> \<tau>. bdd_above (size ` ?terms \<tau>)" 
  define crit where "crit = (\<lambda> (\<tau> :: 't,fs :: ('f \<times> 't list) list). \<forall> \<tau>s \<in> set (map snd fs). \<forall> \<tau> \<in> set \<tau>s. \<tau> \<notin> m_inf)" 
  define S where "S \<tau>' = size ` {t. t : \<tau>' in \<T>(C,E)}" for \<tau>'
  define M where "M \<tau>' = Maximum (S \<tau>')" for \<tau>'
  define M' where "M' \<sigma>s = sum_list (map M \<sigma>s) + (1 + length \<sigma>s)" for \<sigma>s
  define L where "L = [ \<sigma>s . (\<tau>,cs) <- Cs, (f,\<sigma>s) <- cs]" 
  define N where "N = max_list (map M' L)" 
  obtain fin ls' where part: "partition crit ls = (fin, ls')" by force
  {
    fix \<tau> cs
    assume inCs: "(\<tau>,cs) \<in> set Cs" 
    have nonempty:"\<exists> t. t : \<tau> in \<T>(C,E)"
    proof -
      from inhabitet[rule_format, OF inCs] obtain f \<sigma>s where "(f,\<sigma>s) \<in> set cs" by (cases cs,auto )
      with inCs have "((f,\<sigma>s),\<tau>) \<in> set Cs'" unfolding Cs' by auto
      hence fC: "f : \<sigma>s \<rightarrow> \<tau> in C" using dist(2) unfolding C_Cs
        by (meson fun_hastype_def map_of_is_SomeI)
      hence "\<forall>\<sigma>. \<exists> t. \<sigma> \<in> set \<sigma>s \<longrightarrow> t : \<sigma> in \<T>(C,E)" using arg_types_inhabitet[rule_format, of f \<sigma>s \<tau>] by auto
      from choice[OF this] obtain t where "\<sigma> \<in> set \<sigma>s \<Longrightarrow> t \<sigma> : \<sigma> in \<T>(C,E)" for \<sigma> by auto
      hence "Fun f (map t \<sigma>s) : \<tau> in \<T>(C,E)" using list_all2_conv_all_nth 
        apply (intro Fun_hastypeI[OF fC]) by (simp add: list_all2_conv_all_nth)
      then show ?thesis by auto
    qed
  } note inhabited = this
  
  define cards' where "cards' = finfun_update_all (map fst fin) (\<lambda> \<tau>. compute_card_of_sort \<tau> (the (map_of ls \<tau>)) cards) cards"  
  {
    fix \<tau>
    assume asm: "\<tau> \<in> fst ` set fin"
    let ?TT = "?terms \<tau>" 
    from asm obtain cs where tau_cs_fin: "(\<tau>,cs) \<in> set fin" by auto
    hence tau_ls: "(\<tau>,cs) \<in> set ls" using part by auto
    with dist(1) \<open>set ls \<subseteq> set Cs\<close> 
    have map: "map_of Cs \<tau> = Some cs" "map_of ls \<tau> = Some cs" 
      by (metis (no_types, opaque_lifting) eq_key_imp_eq_value map_of_SomeD subsetD weak_map_of_SomeI)+
    from asm have cards': "cards' $ \<tau> = compute_card_of_sort \<tau> cs cards" unfolding cards'_def by (auto simp: map)
    from part asm have tau_fin: "\<tau> \<in> set (map fst fin)" by auto
    {
      fix f \<sigma>s
      have "f : \<sigma>s \<rightarrow> \<tau> in C \<longleftrightarrow> ((f,\<sigma>s),\<tau>) \<in> set Cs'" 
      proof
        assume "f : \<sigma>s \<rightarrow> \<tau> in C" 
        hence "map_of Cs' (f,\<sigma>s) = Some \<tau>" unfolding C_Cs by (rule fun_hastypeD)
        thus "((f,\<sigma>s),\<tau>) \<in> set Cs'" by (rule map_of_SomeD)
      next
        assume "((f, \<sigma>s), \<tau>) \<in> set Cs'" 
        hence "map_of Cs' (f, \<sigma>s) = Some \<tau>" using dist(2) by simp
        thus "f : \<sigma>s \<rightarrow> \<tau> in C" unfolding C_Cs by (rule fun_hastypeI)
      qed
      also have "\<dots> \<longleftrightarrow> (\<exists> cs. (\<tau>, cs) \<in> set Cs \<and> (f,\<sigma>s) \<in> set cs)" 
        unfolding Cs' by auto
      also have "\<dots> \<longleftrightarrow> (\<exists> cs. map_of Cs \<tau> = Some cs \<and> (f,\<sigma>s) \<in> set cs)" 
        using dist(1) by simp
      also have "\<dots> \<longleftrightarrow> (f,\<sigma>s) \<in> set cs" unfolding map by auto
      finally have "(f : \<sigma>s \<rightarrow> \<tau> in C) = ((f, \<sigma>s) \<in> set cs)" by auto
    } note C_to_cs = this

    define T where "T \<sigma> = ?terms \<sigma>" for \<sigma> (* hide internals *)
    have to_ls: "{ts. ts :\<^sub>l \<sigma>s in \<T>(C,E)} = listset (map T \<sigma>s)" for \<sigma>s
      by (intro set_eqI, unfold listset_conv_nth, auto simp: T_def list_all2_conv_all_nth)
    {
      fix f \<sigma>s \<sigma>
      assume in_cs: "(f, \<sigma>s) \<in> set cs" "\<sigma> \<in> set \<sigma>s" 
      from tau_cs_fin part have "crit (\<tau>,cs)" by auto
      from this[unfolded crit_def split] in_cs have "\<sigma> \<notin> m_inf" by auto
      with 1(6) have "cards $ \<sigma> = card (T \<sigma>)" and "finite (T \<sigma>)" by (auto simp: T_def)
    } note \<sigma>s_infos = this

    have "?TT = { Fun f ts | f ts \<sigma>s. f : \<sigma>s \<rightarrow> \<tau> in C \<and> ts :\<^sub>l \<sigma>s in \<T>(C,E)}" (is "_ = ?FunApps")
    proof (intro set_eqI)
      fix t
      {
        assume "t : \<tau> in \<T>(C,E)"
        hence "t \<in> ?FunApps" by (induct, auto simp: E)
      }
      moreover
      {
        assume "t \<in> ?FunApps" 
        hence "t : \<tau> in \<T>(C,E)" by (auto intro: Fun_hastypeI)
      }
      ultimately show "t \<in> ?TT \<longleftrightarrow> t \<in> ?FunApps" by auto
    qed 
    also have "\<dots> = { Fun f ts | f ts \<sigma>s. (f, \<sigma>s) \<in> set cs \<and> ts :\<^sub>l \<sigma>s in \<T>(C,E)}" unfolding C_to_cs ..
    also have "\<dots> = (\<lambda> (f, ts). Fun f ts) ` (\<Union> (f, \<sigma>s) \<in> set cs. Pair f ` { ts. ts :\<^sub>l \<sigma>s in \<T>(C,E)})" (is "_ = ?f ` ?A") by auto
    finally have TTfA: "?TT = ?f ` ?A" .
    have finPair: "finite (Pair f ` A) = finite A" for f :: 'f and A :: "('f, 'v) Term.term list set" 
      by (intro finite_image_iff inj_onI, auto)
    have inj: "inj ?f" by (intro injI, auto)
    from inj have card: "card ?TT = card ?A"  
      unfolding TTfA by (meson UNIV_I card_image inj_on_def)
    also have "\<dots> = (\<Sum>i\<in>set cs. card (case i of (f, \<sigma>s) \<Rightarrow> Pair f ` listset (map T \<sigma>s)))" unfolding to_ls
    proof (rule card_UN_disjoint[OF finite_set ballI ballI[OF ballI[OF impI]]], goal_cases)
      case *: (1 f\<sigma>s)
      obtain f \<sigma>s where f\<sigma>s: "f\<sigma>s = (f,\<sigma>s)" by force
      thus ?case using * \<sigma>s_infos(2) by (cases f\<sigma>s, auto intro!: finite_imageI finite_listset)
    next
      case *: (2 f\<sigma>s g\<tau>s)
      obtain f \<sigma>s where f\<sigma>s: "f\<sigma>s = (f,\<sigma>s)" by force
      obtain g \<tau>s where g\<tau>s: "g\<tau>s = (g,\<tau>s)" by force
      show ?case 
      proof (cases "g = f")
        case False
        thus ?thesis unfolding f\<sigma>s g\<tau>s split by auto
      next
        case True
        note f\<tau>s = g\<tau>s[unfolded True]
        show ?thesis
        proof (rule ccontr)
          assume "\<not> ?thesis" 
          from this[unfolded f\<sigma>s f\<tau>s split]
          obtain ts where ts: "ts \<in> listset (map T \<sigma>s)" "ts \<in> listset (map T \<tau>s)" by auto
          hence len: "length \<sigma>s = length ts" "length \<tau>s = length ts" unfolding listset_conv_nth by auto
          from *(3)[unfolded f\<sigma>s f\<tau>s] have "\<sigma>s \<noteq> \<tau>s" by auto
          with len obtain i where i: "i < length ts" and diff: "\<sigma>s ! i \<noteq> \<tau>s ! i"
            by (metis nth_equalityI)
          define ti where "ti = ts ! i" 
          define \<sigma>i where "\<sigma>i = \<sigma>s ! i"
          define \<tau>i where "\<tau>i = \<tau>s ! i"
          note diff = diff[folded \<sigma>i_def \<tau>i_def]
          from ts i have "ti \<in> T \<sigma>i" "ti \<in> T \<tau>i" 
            unfolding ti_def \<sigma>i_def \<tau>i_def listset_conv_nth by auto
          hence ti: "ti : \<sigma>i in \<T>(C,E)" "ti : \<tau>i in \<T>(C,E)" unfolding T_def by auto
          hence "\<sigma>i = \<tau>i" by fastforce
          with diff show False ..
        qed
      qed
    qed
    also have "\<dots> = (\<Sum> f\<sigma>s \<in>set cs. card (listset (map T (snd f\<sigma>s))))" 
    proof (rule sum.cong[OF refl], goal_cases)
      case (1 f\<sigma>s)
      obtain f \<sigma>s where id: "f\<sigma>s = (f,\<sigma>s)" by force
      show ?case unfolding id split snd_conv
        by (rule card_image, auto simp: inj_on_def)
    qed
    also have "\<dots> = (\<Sum> f\<sigma>s \<in>set cs. prod_list (map card (map T (snd f\<sigma>s))))" 
      by (rule sum.cong[OF refl], rule card_listset, insert \<sigma>s_infos, auto)
    also have "\<dots> = (\<Sum> f\<sigma>s \<in>set cs. prod_list (map (($) cards) (snd f\<sigma>s)))" 
      unfolding map_map o_def using \<sigma>s_infos
      by (intro sum.cong[OF refl] arg_cong[of _ _ prod_list], auto)
    also have "\<dots> = sum_list (map (\<lambda> f\<sigma>s. prod_list (map (($) cards) (snd f\<sigma>s))) (remdups cs))" 
      by (rule sum.set_conv_list)
    also have "\<dots> = cards' $ \<tau>" unfolding cards' compute_card_of_sort_def ..
    finally have cards': "card ?TT = cards' $ \<tau>" by auto


    from inj have "finite ?TT = finite ?A"
      by (metis (no_types, lifting) TTfA finite_imageD finite_imageI subset_UNIV subset_inj_on) 
    also have "\<dots> = (\<forall> f \<sigma>s. (f,\<sigma>s) \<in> set cs \<longrightarrow> finite (Pair f ` {ts. ts :\<^sub>l \<sigma>s in \<T>(C,E)}))" 
      by auto
    finally have "finite ?TT = (\<forall> f \<sigma>s. (f,\<sigma>s) \<in> set cs \<longrightarrow> finite {ts. ts :\<^sub>l \<sigma>s in \<T>(C,E)})" 
      unfolding finPair by auto
    also have "\<dots> = True" unfolding to_ls using \<sigma>s_infos(2) by (auto intro!: finite_listset)
    finally have fin: "finite ?TT" by simp 

    from fin cards'
    have "cards' $ \<tau> = card (?terms \<tau>)" "finite (?terms \<tau>)" "?fin \<tau>" by auto
  } note fin = this
    
  show ?case 
  proof (cases "fin = []")
    case False
    hence "compute_inf_card_main m_inf cards ls = compute_inf_card_main (m_inf - set (map fst fin)) cards' ls'" 
      unfolding compute_inf_card_main.simps[of m_inf] part[unfolded crit_def] cards'_def Let_def by auto
    also have "\<dots> = ({\<tau>. \<not> ?fin \<tau>}, \<lambda> \<tau>. card (?terms \<tau>))" 
    proof (rule 1(1)[OF refl part[unfolded crit_def, symmetric] False])
      show "set ls' \<subseteq> set Cs" using 1(3) part by auto
      show "fst ` (set Cs - set ls') \<inter> (m_inf - set (map fst fin)) = {}" using 1(3-4) part by force
      show "m_inf - set (map fst fin) \<subseteq> fst ` set ls'" using 1(5) part by force
      show "\<forall>\<tau>. \<tau> \<notin> m_inf - set (map fst fin) \<longrightarrow> cards' $ \<tau> = card (?terms \<tau>) \<and> finite (?terms \<tau>)"
      proof (intro allI impI)
        fix \<tau>
        assume nmem: "\<tau> \<notin> m_inf - set (map fst fin)" 
        show "cards' $ \<tau> = card (?terms \<tau>) \<and> finite (?terms \<tau>)" 
        proof (cases "\<tau> \<in> set (map fst fin)")
          case False
          with nmem have tau: "\<tau> \<notin> m_inf" by auto
          with False 1(6)[rule_format, OF this] show ?thesis
            unfolding cards'_def by auto
        next
          case True
          with fin show ?thesis by auto
        qed
      qed
      thus "\<forall>\<tau>. \<tau> \<notin> m_inf - set (map fst fin) \<longrightarrow> ?fin \<tau>" by force
      show "\<forall>\<tau>. \<tau> \<in> m_inf - set (map fst fin) \<longrightarrow> cards' $ \<tau> = 0" using 1(7) unfolding cards'_def 
        by auto
    qed (auto simp: cards'_def)
    finally show ?thesis .
  next
    case True
    let ?cards = "\<lambda>\<tau>. cards $ \<tau>" 
    have m_inf: "m_inf = {\<tau>. \<not> ?fin \<tau>}" 
    proof
      show "{\<tau>. \<not> ?fin \<tau>} \<subseteq> m_inf" using fin 1(2) by auto
      {
        fix \<tau>
        assume "\<tau> \<in> m_inf" 
        with 1(5) obtain cs where mem: "(\<tau>,cs) \<in> set ls" by auto
        from part True have ls': "ls' = ls" by (induct ls arbitrary: ls', auto)
        from partition_P[OF part, unfolded ls']
        have "\<And> e. e \<in> set ls \<Longrightarrow> \<not> crit e" by auto
        from this[OF mem, unfolded crit_def split]
        obtain c \<tau>s \<tau>' where *: "(c,\<tau>s) \<in> set cs" "\<tau>' \<in> set \<tau>s" "\<tau>' \<in> m_inf" by auto
        from mem 1(2-) have "(\<tau>,cs) \<in> set Cs" by auto
        with * have "((c,\<tau>s),\<tau>) \<in> set Cs'" unfolding Cs' by force
        with dist(2) have "map_of Cs' ((c,\<tau>s)) = Some \<tau>" by simp
        from this[folded C_Cs] have c: "c : \<tau>s \<rightarrow> \<tau> in C" unfolding fun_hastype_def .
        from arg_types_inhabitet this have "\<forall> \<sigma>. \<exists> t. \<sigma> \<in> set \<tau>s \<longrightarrow> t : \<sigma> in \<T>(C,E)" by auto
        from choice[OF this] obtain t where "\<And> \<sigma>. \<sigma> \<in> set \<tau>s \<Longrightarrow> t \<sigma> : \<sigma> in \<T>(C,E)" by auto
        hence list: "map t \<tau>s :\<^sub>l \<tau>s in \<T>(C,E)" by (simp add: list_all2_conv_all_nth)
        with c have "Fun c (map t \<tau>s) : \<tau> in \<T>(C,E)" by (intro Fun_hastypeI)
        with * c list have "\<exists> c \<tau>s \<tau>' ts. Fun c ts : \<tau> in \<T>(C,E) \<and> ts :\<^sub>l \<tau>s in \<T>(C,E) \<and> c : \<tau>s \<rightarrow> \<tau> in C \<and> \<tau>' \<in> set \<tau>s \<and> \<tau>' \<in> m_inf" 
          by blast
      } note m_invD = this
      {
        fix n :: nat
        have "\<tau> \<in> m_inf \<Longrightarrow> \<exists> t. t : \<tau> in \<T>(C,E) \<and> size t \<ge> n" for \<tau>
        proof (induct n arbitrary: \<tau>)
          case (0 \<tau>)
          from m_invD[OF 0] show ?case by blast
        next
          case (Suc n \<tau>)
          from m_invD[OF Suc(2)] obtain c \<tau>s \<tau>' ts
            where *: "ts :\<^sub>l \<tau>s in \<T>(C,E)" "c : \<tau>s \<rightarrow> \<tau> in C" "\<tau>' \<in> set \<tau>s" "\<tau>' \<in> m_inf" 
            by auto
          from *(1)[unfolded list_all2_conv_all_nth] *(3)[unfolded set_conv_nth]
          obtain i where i: "i < length \<tau>s" and tsi:"ts ! i : \<tau>' in \<T>(C,E)" and len: "length ts = length \<tau>s" by auto
          from Suc(1)[OF *(4)] obtain t where t:"t : \<tau>' in \<T>(C,E)" and ns:"n \<le> size t" by auto
          define ts' where "ts' = ts[i := t]" 
          have "ts' :\<^sub>l \<tau>s in \<T>(C,E)" using list_all2_conv_all_nth unfolding ts'_def 
            by (metis "*"(1) tsi has_same_type i list_all2_update_cong list_update_same_conv t(1))
          hence **:"Fun c ts' : \<tau> in \<T>(C,E)" apply (intro Fun_hastypeI[OF *(2)]) by fastforce 
          have "t \<in> set ts'" unfolding ts'_def using t 
            by (simp add: i len set_update_memI)
          hence "size (Fun c ts') \<ge> Suc n" using * 
            by (simp add: size_list_estimation' ns)
          thus ?case using ** by blast
        qed
      } note main = this
      show "m_inf \<subseteq> {\<tau>. \<not> ?fin \<tau>}"  
      proof (standard, standard)
        fix \<tau>
        assume asm: "\<tau> \<in> m_inf"         
        have "\<exists>t. t : \<tau> in \<T>(C,E) \<and> n < size t" for n using main[OF asm, of "Suc n"] by auto
        thus "\<not> ?fin \<tau>"
          by (metis bdd_above_Maximum_nat imageI mem_Collect_eq order.strict_iff)
      qed
    qed
    from True have "compute_inf_card_main m_inf cards ls = (m_inf, ?cards)" 
      unfolding compute_inf_card_main.simps[of m_inf] part[unfolded crit_def] by auto
    also have "?cards = (\<lambda> \<tau>. card (?terms \<tau>))" 
    proof (intro ext)
      fix \<tau>
      show "cards $ \<tau> = card (?terms \<tau>)" 
      proof (cases "\<tau> \<in> m_inf")
        case False
        thus ?thesis using 1(6) by auto
      next
        case True
        define TT where "TT = ?terms \<tau>" 
        from True m_inf have "\<not> bdd_above (size ` TT)" unfolding TT_def by auto
        hence "infinite TT" by auto
        hence "card TT = 0" by auto
        thus ?thesis unfolding TT_def using True 1(7) by auto
      qed
    qed
    finally show ?thesis using m_inf by auto
  qed
qed

definition compute_inf_card_sorts :: "(('f \<times> 't list) \<times> 't)list \<Rightarrow> 't set \<times> ('t \<Rightarrow> nat)" where
  "compute_inf_card_sorts Cs = (let 
       Cs' = map (\<lambda> \<tau>. (\<tau>, map fst (filter(\<lambda>f. snd f = \<tau>) Cs))) (remdups (map snd Cs))
    in compute_inf_card_main (set (map fst Cs')) (K$ 0) Cs')" 

lemma compute_inf_card_sorts:
  fixes E :: "'v \<rightharpoonup> 't" and C :: "('f,'t)ssig"
  assumes E: "E = \<emptyset>" 
  and C_Cs: "C = map_of Cs" 
  and arg_types_inhabitet: "\<forall> f \<tau>s \<tau> \<tau>'. f : \<tau>s \<rightarrow> \<tau> in C \<longrightarrow> \<tau>' \<in> set \<tau>s \<longrightarrow> (\<exists> t. t : \<tau>' in \<T>(C,E))"
  and dist: "distinct (map fst Cs)" 
shows "compute_inf_card_sorts Cs = (
   {\<tau>. \<not> bdd_above (size ` {t. t : \<tau> in \<T>(C,E)})},
   \<lambda> \<tau>. card {t. t : \<tau> in \<T>(C,E)})" (is "_ = (?inf, ?cards)")
proof -
  define taus where "taus = remdups (map snd Cs)" 
  define Cs' where "Cs' = map (\<lambda> \<tau>. (\<tau>, map fst (filter(\<lambda>f. snd f = \<tau>) Cs))) taus" 
  have "compute_inf_card_sorts Cs = compute_inf_card_main (set (map fst Cs')) (K$ 0) Cs'" 
    unfolding compute_inf_card_sorts_def taus_def Cs'_def Let_def by auto
  also have "\<dots> = (?inf, ?cards)"
  proof (rule compute_inf_card_main[OF E C_Cs _ arg_types_inhabitet _ dist _ _ subset_refl])   
    have "distinct taus" unfolding taus_def by auto
    thus "distinct (map fst Cs')" unfolding Cs'_def map_map o_def fst_conv by auto
    show "set Cs = set (concat (map (\<lambda>(\<tau>, fs). map (\<lambda>f. (f, \<tau>)) fs) Cs'))" 
      unfolding Cs'_def taus_def by force
    show "\<forall>\<tau> fs. (\<tau>, fs) \<in> set Cs' \<longrightarrow> set fs \<noteq> {}" 
      unfolding Cs'_def taus_def by (force simp: filter_empty_conv)
    show "fst ` (set Cs' - set Cs') \<inter> set (map fst Cs') = {}" by auto
    show "set (map fst Cs') \<subseteq> fst ` set Cs'" by auto
    have "\<forall>\<tau>. \<tau> \<notin> set (map fst Cs') \<longrightarrow> {t. t : \<tau> in \<T>(C,E)} = {}" 
    proof (intro allI impI)
      fix \<tau>
      assume "\<tau> \<notin> set (map fst Cs')" 
      hence "\<tau> \<notin> snd ` set Cs" unfolding Cs'_def taus_def by auto
      hence diff: "C f \<noteq> Some \<tau>" for f unfolding C_Cs
        by (metis Some_eq_map_of_iff dist imageI snd_conv)
      {
        fix t
        assume "t : \<tau> in \<T>(C,E)" 
        hence False using diff unfolding E
        proof induct
          case (Fun f ss \<sigma>s \<tau>)
          from Fun(1,4) show False unfolding fun_hastype_def by auto
        qed auto
      }
      thus id: "{t. t : \<tau> in \<T>(C,E)} = {}" by auto
    qed
    then show "\<forall>\<tau>. \<tau> \<notin> set (map fst Cs') \<longrightarrow> bdd_above (size ` {t. t : \<tau> in \<T>(C,E)})" 
      "\<forall>\<tau>. \<tau> \<notin> set (map fst Cs') \<longrightarrow> (K$ 0) $ \<tau> = card {t. t : \<tau> in \<T>(C,E)} \<and> finite {t. t : \<tau> in \<T>(C,E)}" 
        by auto         
  qed auto
  finally show ?thesis .
qed
end

definition compute_inf_sorts :: "(('f \<times> 't list) \<times> 't)list \<Rightarrow> 't set" where
  "compute_inf_sorts Cs = fst (compute_inf_card_sorts Cs)" 

lemma compute_inf_sorts:
  fixes E :: "'v \<rightharpoonup> 't" and C :: "('f,'t)ssig"
  assumes E: "E = \<emptyset>" 
  and C_Cs: "C = map_of Cs" 
  and arg_types_inhabitet: "\<forall> f \<tau>s \<tau> \<tau>'. f : \<tau>s \<rightarrow> \<tau> in C \<longrightarrow> \<tau>' \<in> set \<tau>s \<longrightarrow> (\<exists> t. t : \<tau>' in \<T>(C,E))"
  and dist: "distinct (map fst Cs)" 
shows "compute_inf_sorts Cs = {\<tau>. \<not> bdd_above (size ` {t. t : \<tau> in \<T>(C,E)})}"
  unfolding compute_inf_sorts_def compute_inf_card_sorts[OF assms] by simp

end
