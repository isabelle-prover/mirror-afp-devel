subsection \<open>Algorithm to Detect all Implicit Equalities in \<open>\<rat>\<close>\<close>

text \<open>Use incremental simplex algorithm to recursively detect all
  implied equalities.\<close>

theory Equality_Detection_Impl
  imports 
    Equality_Detection_Theory
    Simplex.Simplex_Incremental
    Deriving.Compare_Instances
begin

lemma indexed_sat_mono: "(S,v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s cs \<Longrightarrow> T \<subseteq> S \<Longrightarrow> (T,v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s cs" 
  by auto

lemma assert_all_simplex_plain_unsat: assumes "invariant_simplex cs J s"
  and "assert_all_simplex K s = Unsat I" 
shows "\<not> (set K \<union> J, v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set cs"
proof -
  from assert_all_simplex_unsat[OF assms]
  show ?thesis unfolding minimal_unsat_core_def by force
qed


lemma check_simplex_plain_unsat: assumes "invariant_simplex cs J s"
  and "check_simplex s = (s',Some I)" 
shows "\<not> (J, v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set cs"
proof -
  from check_simplex_unsat[OF assms]
  show ?thesis unfolding minimal_unsat_core_def by force
qed
  

hide_const (open) Congruence.eq

fun le_of_constraint :: "constraint \<Rightarrow> rat le_constraint" where
  "le_of_constraint (LEQ p c) = Le_Constraint Leq_Rel p c" 
| "le_of_constraint (LT p c) = Le_Constraint Lt_Rel p c" 
| "le_of_constraint (GEQ p c) = Le_Constraint Leq_Rel (-p) (-c)" 
| "le_of_constraint (GT p c) = Le_Constraint Lt_Rel (-p) (-c)" 
 

fun poly_of_constraint :: "constraint \<Rightarrow> linear_poly" where
  "poly_of_constraint (LEQ p c) = p" 
| "poly_of_constraint (LT p c) = p" 
| "poly_of_constraint (GEQ p c) = (-p)" 
| "poly_of_constraint (GT p c) = (-p)" 
 
fun const_of_constraint :: "constraint \<Rightarrow> rat" where
  "const_of_constraint (LEQ p c) = c" 
| "const_of_constraint (LT p c) = c" 
| "const_of_constraint (GEQ p c) = (-c)" 
| "const_of_constraint (GT p c) = (-c)" 

fun is_no_equality :: "constraint \<Rightarrow> bool" where
  "is_no_equality (EQ p c) = False" 
| "is_no_equality _ = True" 

fun is_equality :: "constraint \<Rightarrow> bool" where
  "is_equality (EQ p c) = True" 
| "is_equality _ = False" 

lemma le_of_constraint: "is_no_equality c \<Longrightarrow> v \<Turnstile>\<^sub>c c \<longleftrightarrow> (v \<Turnstile>\<^sub>l\<^sub>e le_of_constraint c)" 
  by (cases c, auto simp: valuate_uminus)


lemma le_of_constraints: "Ball cs is_no_equality \<Longrightarrow> v \<Turnstile>\<^sub>c\<^sub>s cs \<longleftrightarrow> (\<forall> c \<in> cs. v \<Turnstile>\<^sub>l\<^sub>e le_of_constraint c)" 
  using le_of_constraint by auto

fun is_strict :: "constraint \<Rightarrow> bool" where
  "is_strict (GT _ _) = True" 
| "is_strict (LT _ _) = True" 
| "is_strict _ = False" 

fun is_nstrict :: "constraint \<Rightarrow> bool" where
  "is_nstrict (GEQ _ _) = True" 
| "is_nstrict (LEQ _ _) = True" 
| "is_nstrict _ = False" 

lemma is_equality_iff: "is_equality c = (\<not> is_strict c \<and> \<not> is_nstrict c)" 
  by (cases c, auto)

lemma is_nstrict_iff: "is_nstrict c = (\<not> is_strict c \<and> \<not> is_equality c)" 
  by (cases c, auto)

fun make_strict :: "constraint \<Rightarrow> constraint" where
  "make_strict (GEQ p c) = GT p c"
| "make_strict (LEQ p c) = LT p c"
| "make_strict c = c"

fun make_equality :: "constraint \<Rightarrow> constraint" where
  "make_equality (GEQ p c) = EQ p c"
| "make_equality (LEQ p c) = EQ p c"
| "make_equality c = c" 

fun make_ineq :: "constraint \<Rightarrow> constraint" where
  "make_ineq (GEQ p c) = GEQ p c"
| "make_ineq (LEQ p c) = LEQ p c"
| "make_ineq (EQ p c) = LEQ p c"

fun make_flipped_ineq :: "constraint \<Rightarrow> constraint" where
  "make_flipped_ineq (GEQ p c) = LEQ p c"
| "make_flipped_ineq (LEQ p c) = GEQ p c"
| "make_flipped_ineq (EQ p c) = GEQ p c"

lemma poly_const_repr: assumes "is_nstrict c" 
  shows "le_of_constraint c = Le_Constraint Leq_Rel (poly_of_constraint c) (const_of_constraint c)"
    "le_of_constraint (make_strict c) = Le_Constraint Lt_Rel (poly_of_constraint c) (const_of_constraint c)"
    "le_of_constraint (make_flipped_ineq c) = Le_Constraint Leq_Rel (- poly_of_constraint c) (- const_of_constraint c)"
  using assms by (cases c, auto)+

lemma poly_const_repr_set: assumes "Ball cs is_nstrict" 
  shows "le_of_constraint ` cs = (\<lambda> c. Le_Constraint Leq_Rel (poly_of_constraint c) (const_of_constraint c)) ` cs"
    "le_of_constraint ` (make_strict ` cs) = (\<lambda> c. Le_Constraint Lt_Rel (poly_of_constraint c) (const_of_constraint c)) ` cs"
  subgoal using assms poly_const_repr(1) by simp
  subgoal using assms poly_const_repr(2) unfolding image_comp o_def by auto
  done


datatype eqd_index = 
  Ineq nat | (* inequality, non-strict *)
  FIneq nat | (* Flipped inequality *)
  SIneq nat | (* strict inequality *)
  TmpSIneq nat (* temporary strict inequality *)

fun num_of_index :: "eqd_index \<Rightarrow> nat" where
  "num_of_index (FIneq n) = n" 
| "num_of_index (Ineq n) = n" 
| "num_of_index (SIneq n) = n" 
| "num_of_index (TmpSIneq n) = n" 

derive compare_order eqd_index

fun index_constraint :: "nat \<times> constraint \<Rightarrow> eqd_index i_constraint list" where
  "index_constraint (n, c) = (
     if is_nstrict c then [(Ineq n, c), (FIneq n, make_flipped_ineq c), (TmpSIneq n, make_strict c)] else
     if is_strict c then [(SIneq n, c)] else 
     [(Ineq n, make_ineq c), (FIneq n, make_flipped_ineq c)]
        )" 

definition init_constraints :: "constraint list \<Rightarrow> eqd_index i_constraint list \<times> nat list \<times> nat list \<times> nat list" where
  "init_constraints cs = (let 
     ics' = zip [0 ..< length cs] cs;
     ics = concat (map index_constraint ics');
     ineqs = map fst (filter (is_nstrict o snd) ics');
     sneqs = map fst (filter (is_strict o snd) ics');
     eqs = map fst (filter (is_equality o snd) ics')
    in (ics, ineqs, sneqs, eqs))"

definition index_of :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> eqd_index list" where
  "index_of ineqs sineqs eqs = map SIneq sineqs @ map Ineq eqs @ map FIneq eqs @ map Ineq ineqs" 

context 
  fixes cs :: "constraint list" 
  and ics :: "eqd_index i_constraint list" 
begin

definition cs_of :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> constraint set" where
  "cs_of ineqs sineqs eqs = Simplex.restrict_to (set (index_of ineqs sineqs eqs)) (set ics)" 

lemma init_constraints: assumes init: "init_constraints cs = (ics, ineqs, sineqs, eqs)" 
  shows "v \<Turnstile>\<^sub>c\<^sub>s cs_of ineqs sineqs eqs \<longleftrightarrow> v \<Turnstile>\<^sub>c\<^sub>s set cs"
    "distinct_indices ics" 
    "fst ` set ics = set (map SIneq sineqs @ map Ineq eqs @ map FIneq eqs @ map Ineq ineqs @ map FIneq ineqs @ map TmpSIneq ineqs)" (is "_ = ?l")
    "set eqs = {i. i < length cs \<and> is_equality (cs ! i)}" 
    "set ineqs = {i. i < length cs \<and> is_nstrict (cs ! i)}"
    "set sineqs = {i. i < length cs \<and> is_strict (cs ! i)}" 
    "set ics =
       (\<lambda>i. (Ineq i, make_ineq (cs ! i))) ` set eqs \<union>
       (\<lambda>i. (FIneq i, make_flipped_ineq (cs ! i))) ` set eqs \<union>
       ((\<lambda>i. (Ineq i, cs ! i)) ` set ineqs \<union>
       (\<lambda>i. (FIneq i, make_flipped_ineq (cs ! i))) ` set ineqs \<union>
       (\<lambda>i. (TmpSIneq i, make_strict (cs ! i))) ` set ineqs) \<union>
       (\<lambda>i. (SIneq i, cs ! i)) ` set sineqs" (is "_ = ?Large") 
    "distinct (eqs @ ineqs @ sineqs)" 
    "set (eqs @ ineqs @ sineqs) = {0 ..< length cs}" 
proof -
  let ?R = "Simplex.restrict_to (Ineq ` set ineqs \<union> SIneq ` set sineqs \<union> Ineq ` set eqs \<union> FIneq ` set eqs) (set ics)" 
  let ?n = "length cs" 
  let ?I = "Ineq ` set ineqs \<union> SIneq ` set sineqs \<union> Ineq ` set eqs \<union> FIneq ` set eqs" 
  define ics' where "ics' = zip [0 ..< ?n] cs" 
  from init[unfolded init_constraints_def Let_def, folded ics'_def]
  have ics: "ics = concat (map index_constraint ics')" and
    eqs: "eqs = map fst (filter (is_equality \<circ> snd) ics')" and
    ineqs: "ineqs = map fst (filter (is_nstrict \<circ> snd) ics')" and
    sineqs: "sineqs = map fst (filter (is_strict \<circ> snd) ics')" by auto
  from eqs show eqs': "set eqs = {i. i < ?n \<and> is_equality (cs ! i)}" 
    by (force simp: set_zip ics'_def)
  from ineqs show ineqs': "set ineqs = {i. i < ?n \<and> is_nstrict (cs ! i)}" 
    by (force simp: set_zip ics'_def)
  from sineqs show sineqs': "set sineqs = {i. i < ?n \<and> is_strict (cs ! i)}" 
    by (force simp: set_zip ics'_def)
  show "set (eqs @ ineqs @ sineqs) = {0 ..< ?n}" 
    unfolding set_append eqs' ineqs' sineqs' 
    by (auto simp: is_nstrict_iff)
  show "distinct (eqs @ ineqs @ sineqs)" unfolding distinct_append
    unfolding ineqs eqs sineqs ics'_def
    by (auto intro: distinct_map_filter simp: set_zip is_nstrict_iff)
      (simp add: is_equality_iff)
  from eqs' have eqs'': "i \<in> set eqs \<Longrightarrow> index_constraint (i, cs ! i) = 
     [(Ineq i, make_ineq (cs ! i)), (FIneq i, make_flipped_ineq (cs ! i))]" for i 
    by (cases "cs ! i", auto)
  from ineqs' have ineqs'': "i \<in> set ineqs \<Longrightarrow> index_constraint (i, cs ! i) = 
     [(Ineq i, cs ! i), (FIneq i, make_flipped_ineq (cs ! i)), (TmpSIneq i, make_strict (cs ! i))]" for i 
    by (cases "cs ! i", auto)
  from sineqs' have sineqs'': "i \<in> set sineqs \<Longrightarrow> index_constraint (i, cs ! i) = 
     [(SIneq i, cs ! i)]" for i 
    by (cases "cs ! i", auto)
  let ?IC = "\<lambda> I. \<Union> (set ` index_constraint ` (\<lambda>i. (i, cs ! i)) ` I)" 
  have "set ics' = (\<lambda> i. (i, cs ! i)) ` {i. i < ?n}" unfolding ics'_def
    by (force simp: set_zip)
  also have "{i. i < ?n} = set eqs \<union> set ineqs \<union> set sineqs" 
    unfolding ineqs' eqs' sineqs' 
    by (auto simp: is_equality_iff)
  finally have "set ics = ?IC (set eqs \<union> set ineqs \<union> set sineqs)" unfolding ics set_concat set_map
    by auto
  also have "\<dots> = ?IC (set eqs) \<union> ?IC (set ineqs) \<union> ?IC (set sineqs)" by auto
  also have "?IC (set eqs) = (\<lambda> i. (Ineq i, make_ineq (cs ! i))) ` set eqs
      \<union> (\<lambda> i. (FIneq i, make_flipped_ineq (cs ! i))) ` set eqs" 
    using eqs'' by auto
  also have "?IC (set ineqs) = (\<lambda> i. (Ineq i,  cs ! i)) ` set ineqs
      \<union> (\<lambda> i. (FIneq i, make_flipped_ineq (cs ! i))) ` set ineqs
      \<union> (\<lambda> i. (TmpSIneq i, make_strict (cs ! i))) ` set ineqs" 
    using ineqs'' by auto
  also have "?IC (set sineqs) = (\<lambda> i. (SIneq i,  cs ! i)) ` set sineqs" 
    using sineqs'' by auto
  finally show icsL: "set ics = ?Large" by auto
  show "fst ` set ics = ?l" unfolding icsL set_map set_append image_Un image_comp o_def fst_conv
    by auto
  have "distinct (map fst ics')" unfolding ics'_def by auto
  thus dist: "distinct_indices ics" unfolding ics
  proof (induct ics')
    case (Cons ic ics)
    obtain i c where ic: "ic = (i,c)" by force
    {
      fix j
      assume j: "j \<in> fst ` set (index_constraint (i, c))" 
        "j \<in> fst ` (\<Union>a\<in>set ics. set (index_constraint a))" 
      from j(1) have ji: "num_of_index j = i" by (cases c, auto)
      from j(2) obtain i' c' where ic': "(i',c') \<in> set ics" and "j \<in> fst ` set (index_constraint (i',c'))" by force
      from this(2) have ji': "num_of_index j = i'" by (cases c', auto)
      with ji have "i = i'" by auto
      with ic' ic Cons(2) have False by force
    } note tedious = this
    show ?case unfolding ic distinct_indices_def
      apply (simp del: index_constraint.simps, intro conjI)
      subgoal by (cases c, auto)
      subgoal using Cons by (auto simp: distinct_indices_def)
      subgoal using tedious by blast
      done
  qed (simp add: distinct_indices_def)

  show "v \<Turnstile>\<^sub>c\<^sub>s cs_of ineqs sineqs eqs \<longleftrightarrow> v \<Turnstile>\<^sub>c\<^sub>s set cs" 
  proof
    assume v: "v \<Turnstile>\<^sub>c\<^sub>s cs_of ineqs sineqs eqs" 
    {
      fix c
      assume "c \<in> set cs"
      then obtain i where c: "c = cs ! i" and i: "i < ?n" unfolding set_conv_nth by auto
      hence ic: "(i,c) \<in> set ics'" unfolding ics'_def set_zip by force
      hence ics: "set (index_constraint (i,c)) \<subseteq> set ics" unfolding ics by force
      consider (e) "is_equality c" | (s) "is_strict c" | (n) "is_nstrict c" by (cases c, auto)
      hence "v \<Turnstile>\<^sub>c c" 
      proof cases
        case e
        hence eqs: "i \<in> set eqs" unfolding eqs using ic by force
        from e have "{(FIneq i, make_flipped_ineq c), (Ineq i, make_ineq c)} \<subseteq> set (index_constraint (i,c))" by (cases c, auto)
        moreover with ics have "{(FIneq i, make_flipped_ineq c), (Ineq i, make_ineq c)} \<subseteq> set ics" by auto
        ultimately have "{make_flipped_ineq c, make_ineq c} \<subseteq> cs_of ineqs sineqs eqs" unfolding cs_of_def using eqs 
          unfolding index_of_def using e by (cases c, force+)
        with v have "v \<Turnstile>\<^sub>c make_flipped_ineq c" "v \<Turnstile>\<^sub>c make_ineq c" by auto
        with e show ?thesis by (cases c, auto)
      next
        case s
        hence sineqs: "i \<in> set sineqs" unfolding sineqs using ic by force
        from s have "(SIneq i, c) \<in> set (index_constraint (i,c))" by (cases c, auto)
        moreover with ics have "(SIneq i, c) \<in> set ics" by auto
        ultimately have "c \<in> cs_of ineqs sineqs eqs" unfolding cs_of_def using sineqs
          unfolding index_of_def using s by (cases c, force+)
        with v show "v \<Turnstile>\<^sub>c c" by auto
      next
        case n
        hence ineq: "i \<in> set ineqs" unfolding ineqs using ic by force
        from n have "(Ineq i, c) \<in> set (index_constraint (i,c))" by (cases c, auto)
        moreover with ics have "(Ineq i, c) \<in> set ics" by auto
        ultimately have "c \<in> cs_of ineqs sineqs eqs" unfolding cs_of_def using ineq
          unfolding index_of_def using n by (cases c, force+)
        with v show "v \<Turnstile>\<^sub>c c" by auto
      qed
    }
    thus "v \<Turnstile>\<^sub>c\<^sub>s set cs" by auto
  next
    assume v: "v \<Turnstile>\<^sub>c\<^sub>s set cs" 
    {
      fix c
      assume "c \<in> cs_of ineqs sineqs eqs"
      hence "c \<in> ?R" unfolding cs_of_def index_of_def by auto
      then obtain i where i: "i \<in> ?I" and ic: "(i,c) \<in> set ics" by force
      from ic[unfolded ics] obtain kd where ic: "(i,c) \<in> set (index_constraint kd)" and mem: "kd \<in> set ics'" by auto
      from mem[unfolded ics'_def] obtain k d where kd: "kd = (k,d)" and d: "d \<in> set cs" and k: "k < ?n" "d = cs ! k" 
        unfolding set_conv_nth by force
      from v d have vd: "v \<Turnstile>\<^sub>c d" by auto
      consider (s) j where "i = SIneq j" "j \<in> set sineqs" | (e) j where "i = Ineq j \<or> i = FIneq j" "j \<in> set eqs" | (n) j where "i = Ineq j" "j \<in> set ineqs" 
        using i by auto
      then have "v \<Turnstile>\<^sub>c c" 
      proof cases
        case n
        from ic[unfolded n kd] have j: "j = k" by (cases d, auto)
        from n(2)[unfolded ineqs j] obtain eq where keq: "(k,eq) \<in> set ics'" and nstr: "is_nstrict eq" by force
        from keq[unfolded ics'_def] k have "eq = d" unfolding set_conv_nth by force
        with nstr have "is_nstrict d" by auto
        with ic[unfolded n kd] have "c = d" by (cases d, auto)
        then show ?thesis using vd by auto
      next
        case e
        from ic e kd have j: "j = k" by (cases d, auto)
        from e(2)[unfolded eqs j] obtain eq where keq: "(k,eq) \<in> set ics'" and iseq: "is_equality eq" by force
        from keq[unfolded ics'_def] k have "eq = d" unfolding set_conv_nth by force
        with iseq have eq: "is_equality d" by auto
        with ic e kd have "c = make_ineq d \<or> c = make_flipped_ineq d" by (cases d, auto)
        then show ?thesis using vd eq by (cases d, auto)
      next
        case s
        from ic[unfolded s kd] have j: "j = k" by (cases d, auto)
        from s(2)[unfolded sineqs j] obtain eq where keq: "(k,eq) \<in> set ics'" and str: "is_strict eq" by force
        from keq[unfolded ics'_def] k have "eq = d" unfolding set_conv_nth by force
        with str have "is_strict d" by auto
        with ic[unfolded s kd] have "c = d" by (cases d, auto)
        then show ?thesis using vd by auto
      qed
    }
    thus "v \<Turnstile>\<^sub>c\<^sub>s cs_of ineqs sineqs eqs" by auto
  qed
qed

definition init_eq_finder_rat :: "(eqd_index simplex_state \<times> nat list \<times> nat list \<times> nat list) option" where
  "init_eq_finder_rat = (case init_constraints cs of (ics, ineqs, sineqs, eqs)
      \<Rightarrow> let s0 = init_simplex ics
       in (case assert_all_simplex (index_of ineqs sineqs eqs) s0
         of Unsat _ \<Rightarrow> None
          | Inr s1 \<Rightarrow> (case check_simplex s1
         of (_, Some _) \<Rightarrow> None
          | (s2, None) \<Rightarrow> Some (s2, ineqs, sineqs, eqs))))" 


partial_function (tailrec) eq_finder_main_rat :: "eqd_index simplex_state \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<times> nat list \<times> (var \<Rightarrow> rat)" where
  [code]: "eq_finder_main_rat s ineq eq = (if ineq = [] then (ineq, eq, solution_simplex s) else let
      cp = checkpoint_simplex s;
      res_strict = (case assert_all_simplex (map TmpSIneq ineq) s  \<comment> \<open>Make all inequalities strict and test sat\<close>
          of Unsat C \<Rightarrow> Inl (s, C)
           | Inr s1 \<Rightarrow> (case check_simplex s1 of
              (s2, None) \<Rightarrow> Inr (solution_simplex s2)
            | (s2, Some C) \<Rightarrow> Inl (backtrack_simplex cp s2, C)))
     in case res_strict of 
       Inr sol \<Rightarrow> (ineq, eq, sol)   \<comment> \<open>if indeed all equalities are strictly sat, then no further equality is implied\<close>
     | Inl (s2, C) \<Rightarrow> let
         eq' = remdups [i. TmpSIneq i <- C]; \<comment> \<open>collect all indices of the strict inequalities within the minimal unsat-core\<close>
              \<comment> \<open>the remdups might not be necessary, however the simplex interfact does not ensure distinctness of C\<close>
         s3 = sum.projr (assert_all_simplex (map FIneq eq') s2); \<comment> \<open>and permantly add the flipped inequalities\<close>
         s4 = fst (check_simplex s3); \<comment> \<open>this check will succeed, no unsat can be reported here\<close>
         ineq' = filter (\<lambda> i. i \<notin> set eq') ineq \<comment> \<open>add eq' from inequalities to equalities and continue\<close>
       in eq_finder_main_rat s4 ineq' (eq' @ eq))" 

definition eq_finder_rat :: "(nat list \<times> (var \<Rightarrow> rat)) option" where
  "eq_finder_rat = (case init_eq_finder_rat of None \<Rightarrow> None
    | Some (s, ineqs, sineqs, eqs) \<Rightarrow> Some (
      case eq_finder_main_rat s ineqs eqs of (ineq, eq, sol)
      \<Rightarrow> (eq, sol)))" 
 
context
  fixes eqs ineqs sineqs:: "nat list" 
  assumes init_cs: "init_constraints cs = (ics, ineqs, sineqs, eqs)" 
begin

definition equiv_to_cs where 
  "equiv_to_cs eq = (\<forall>v. v \<Turnstile>\<^sub>c\<^sub>s set cs = (set (index_of ineqs sineqs eq), v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set ics)"

definition "strict_ineq_sat ineq eq v = ((set (index_of ineqs sineqs eq) \<union> TmpSIneq ` set ineq, v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set ics)"

lemma init_eq_finder_rat: "init_eq_finder_rat = None \<Longrightarrow> \<nexists> v. v \<Turnstile>\<^sub>c\<^sub>s set cs" 
  "init_eq_finder_rat = Some (s, ineq, sineq, eq) \<Longrightarrow> 
      checked_simplex ics (set (index_of ineqs sineqs eq)) s 
    \<and> eq = eqs \<and> ineq = ineqs \<and> sineq = sineqs
    \<and> equiv_to_cs eq
    \<and> distinct (ineq @ sineq @ eq)
    \<and> set (ineq @ sineq @ eq) = {0 ..< length cs}" 
proof (atomize(full), goal_cases)
  case 1
  define s0 where "s0 = init_simplex ics" 
  define I where "I = index_of ineqs sineqs eqs" 
  note init = init_eq_finder_rat_def[unfolded init_cs split Let_def, folded s0_def I_def]
  note init_cs = init_constraints[OF init_cs, unfolded cs_of_def, folded I_def]
  from init_simplex[of ics, folded s0_def]
  have s0: "invariant_simplex ics {} s0" by (rule checked_invariant_simplex)
  show ?case
  proof (cases "assert_all_simplex I s0")
    case Inl (* unsat *)
    from assert_all_simplex_plain_unsat[OF s0 Inl]
    have "\<nexists> v. (set I,v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set ics" by auto
    hence "\<nexists> v. v \<Turnstile>\<^sub>c\<^sub>s set cs" using init_cs(1) by auto
    with Inl init show ?thesis by auto
  next
    case (Inr s1)
    obtain s2 res where ch: "check_simplex s1 = (s2, res)" by force
    note init = init[unfolded Inr ch split sum.simps]
    from assert_all_simplex_ok[OF s0 Inr]
    have s1: "invariant_simplex ics (set I) s1" by auto
    show ?thesis
    proof (cases res)
      case Some
      note ch = ch[unfolded Some]
      from check_simplex_plain_unsat[OF s1 ch] init_cs(1)
        Some ch init 
      show ?thesis by auto
    next
      case None
      note ch = ch[unfolded None]
      note init = init[unfolded None option.simps]
      from check_simplex_ok[OF s1 ch]
      have s2: "checked_simplex ics (set I) s2" .
      from init s2 init_cs(1,8,9) show ?thesis unfolding I_def equiv_to_cs_def by fastforce
    qed
  qed
qed

lemma eq_finder_main_rat: fixes Ineq Eq 
  assumes "checked_simplex ics (set (index_of ineqs sineqs eq)) s" 
  and "set ineq \<subseteq> set ineqs" 
  and "set eqs \<subseteq> set eq \<and> set eq \<union> set ineq = set eqs \<union> set ineqs" 
  and "eq_finder_main_rat s ineq eq = (Ineq, Eq, v_sol)" 
  and "equiv_to_cs eq" 
  and "distinct (ineq @ eq)" 
shows "set Ineq \<subseteq> set ineqs" "set eqs \<subseteq> set Eq" "set Ineq \<union> set Eq = set eqs \<union> set ineqs"  
  and "equiv_to_cs Eq" (* equivalence to original system *)
  and "strict_ineq_sat Ineq Eq v_sol" (* v_sol is a solution where all non-strict inequalities are satisfied strictly *)
  and "distinct (Ineq @ Eq)" 
proof (atomize(full), goal_cases)
  case 1
  show ?case using assms
  proof (induction ineq arbitrary: s eq rule: length_induct)
    case (1 ineq s eq)
    define I where "I = set (index_of ineqs sineqs eq)" 
    note s = "1.prems"(1)[folded I_def]
    note ineq = "1.prems"(2)
    note eq = "1.prems"(3)
    note res = "1.prems"(4)[unfolded eq_finder_main_rat.simps[of _ ineq]]
    note equiv = "1.prems"(5)
    note dist = "1.prems"(6)
    note IH = "1.IH"[rule_format]
    from s have inv: "invariant_simplex ics I s" by (rule checked_invariant_simplex)
    note sol = solution_simplex[OF s refl]
    show ?case
    proof (cases "ineq = []")
      case True
      with res have "Ineq = []" "Eq = eq" "v_sol = solution_simplex s" by auto
      with True have "strict_ineq_sat Ineq Eq v_sol = ((I, solution_simplex s) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set ics)" 
        unfolding strict_ineq_sat_def by (auto simp: I_def)
      with sol have "strict_ineq_sat Ineq Eq v_sol" by auto
      with True res eq ineq equiv sol dist show ?thesis by (auto simp: equiv_to_cs_def strict_ineq_sat_def)
    next
      case False
      hence False: "(ineq = []) = False" by auto
      define cp where "cp = checkpoint_simplex s" 
      let ?J = "I \<union> TmpSIneq ` set ineq" 
      let ?ass = "assert_all_simplex (map TmpSIneq ineq) s" 
      define inner where "inner = (case assert_all_simplex (map TmpSIneq ineq) s of Inl I \<Rightarrow> Inl (s, I)
        | Inr s1 \<Rightarrow> (case check_simplex s1 of (s2, None) \<Rightarrow> Inr (solution_simplex s2) | (s2, Some I) \<Rightarrow> Inl (backtrack_simplex cp s2, I)))" 
      note res = res[unfolded False if_False, folded cp_def, unfolded Let_def, folded inner_def]
      {
        fix s2 C
        assume "inner = Inl (s2, C)" 
        note inner = this[unfolded inner_def sum.simps] 
        have "set C \<subseteq> ?J \<and> minimal_unsat_core (set C) ics \<and> invariant_simplex ics I s2"
        proof (cases ?ass)
          case unsat: (Inl D)
          with inner have "D = C" "s2 = s" by auto
          with assert_all_simplex_unsat[OF inv unsat] inv show ?thesis by auto
        next
          case ass: (Inr s1)
          note inner = inner[unfolded ass sum.simps]
          from inner obtain s3 where check: "check_simplex s1 = (s3, Some C)" 
            and s2: "s2 = backtrack_simplex cp s3" 
            by (cases "check_simplex s1", auto split: option.splits)
          note s1 = assert_all_simplex_ok[OF inv ass]
          from check_simplex_unsat[OF s1 check]
          have s3: "weak_invariant_simplex ics ?J s3" and C: "set C \<subseteq> ?J" "minimal_unsat_core (set C) ics" by auto
          from backtrack_simplex[OF s cp_def[symmetric] s3 s2[symmetric]]
          have s2: "invariant_simplex ics I s2" by auto
          from s2 C show ?thesis by auto
        qed
      } note inner_Some = this

      show ?thesis
      proof (cases inner)
        case (Inr sol)
        note inner = this[unfolded inner_def] 
        from inner obtain s1 where ass: "?ass = Inr s1" by (cases ?ass, auto)
        note inner = inner[unfolded ass sum.simps]
        from inner obtain s2 where check: "check_simplex s1 = (s2, None)" by (cases "check_simplex s1", auto split: option.splits)
        from solution_simplex[OF check_simplex_ok[OF assert_all_simplex_ok[OF inv ass] check]]
        have "(?J, sol) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set ics" using inner[unfolded check split option.simps] by auto
        hence str: "strict_ineq_sat ineq eq sol" unfolding I_def strict_ineq_sat_def by auto
        from res[unfolded Inr] have id: "Ineq = ineq" "Eq = eq" "v_sol = sol" by auto
        show ?thesis unfolding id using dist eq ineq equiv str by auto
      next
        case (Inl pair)
        then obtain s2 C where inner: "inner = Inl (s2, C)" by (cases pair, auto)
        from inner_Some[OF this]
        have C: "set C \<subseteq> I \<union> TmpSIneq ` set ineq" 
          and unsat: "minimal_unsat_core (set C) ics" 
          and s2: "invariant_simplex ics I s2" 
          by auto
        define eq' where "eq' = remdups [i. TmpSIneq i <- C]" 
        have ran: "range TmpSIneq \<inter> I = {}" unfolding I_def index_of_def by auto
        {
          assume "eq' = []" 
          hence CI: "set C \<subseteq> I" using C ran eq'_def by force
          from unsat have "\<nexists> v. (set C, v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set ics" unfolding minimal_unsat_core_def by auto
          with indexed_sat_mono[OF sol CI] have False by auto
        }
        hence eq': "eq' \<noteq> []" by auto
        let ?eq = "eq' @ eq" 
        define s3 where "s3 = sum.projr (assert_all_simplex (map FIneq eq') s2)" 
        define s4 where "s4 = fst (check_simplex s3)" 
        define ineq' where "ineq' = filter (\<lambda>i. i \<notin> set eq') ineq" 
        have eq'_ineq: "set eq' \<subseteq> set ineq" using C ran unfolding eq'_def by auto
        have eq_new: "set eqs \<subseteq> set ?eq \<and> set ?eq \<union> set ineq' = set eqs \<union> set ineqs" using eq'_ineq ineq eq
          by (auto simp: ineq'_def)
        have dist: "distinct (ineq' @ eq' @ eq)" using dist unfolding ineq'_def using eq'_ineq
            unfolding eq'_def by auto
        have ineq_new: "set ineq' \<subseteq> set ineqs" using ineq unfolding ineq'_def by auto
        from eq' eq'_ineq have len: "length ineq' < length ineq" unfolding ineq'_def
          by (metis empty_filter_conv filter_True length_filter_less subsetD)
        note res = res[unfolded inner sum.simps split, folded eq'_def, folded s3_def, folded ineq'_def s4_def]
        show ?thesis 
        proof (rule IH[OF len _ ineq_new eq_new res _ dist])
          define I' where "I' = index_of ineqs sineqs ?eq" 
          have II': "set I' = set (map FIneq eq') \<union> I" unfolding I'_def I_def index_of_def using ineq eq'_ineq by auto
          show equiv_new: "equiv_to_cs ?eq" 
          proof -
            define c_of where "c_of I = Simplex.restrict_to I (set ics)" for I  
            have "?thesis \<longleftrightarrow> (\<forall>v. (I, v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set ics \<longleftrightarrow> (FIneq ` set eq' \<union> I, v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set ics)" 
              unfolding equiv_to_cs_def using equiv[unfolded equiv_to_cs_def]
              unfolding I'_def[symmetric] I_def[symmetric] II' by auto
            also have "\<dots> \<longleftrightarrow> (\<forall>v. v \<Turnstile>\<^sub>c\<^sub>s c_of I \<longrightarrow> v \<Turnstile>\<^sub>c\<^sub>s c_of (FIneq ` set eq'))"
              unfolding c_of_def by auto
            also have "\<dots>" 
            proof (intro allI impI)
              fix v
              assume v: "v \<Turnstile>\<^sub>c\<^sub>s c_of I" 
              let ?Ineq = "Equality_Detection_Impl.Ineq ` set ineq"  
              let ?SIneq = "Equality_Detection_Impl.TmpSIneq ` set ineq"
              from init_constraints[OF init_cs]
              have dist: "distinct (map fst ics)" unfolding distinct_indices_def by auto
              {
                fix c i
                assume c: "c \<in> c_of {i}" 
                have "c_of {i} = {c}" 
                proof -
                  {
                    fix d
                    assume "d \<in> c_of {i}" 
                    from this[unfolded c_of_def] 
                    have d: "(i, d) \<in> set ics" by force
                    from c[unfolded c_of_def]
                    have c: "(i, c) \<in> set ics" by force
                    from c d dist have "c = d" by (metis eq_key_imp_eq_value)
                  }
                  with c show ?thesis by blast
                qed
              } note c_of_inj = this

              let ?n = "length cs" 
              {
                note init_cs' = init_cs[unfolded init_constraints_def Let_def]
                fix i
                assume "i \<in> set ineq" 
                with ineq have "i \<in> set ineqs" by auto
                with init_cs'
                have "i \<in> set (map fst (filter (is_nstrict \<circ> snd) (zip [0..<length cs] cs)))" by auto
                hence i_n: "i < ?n" and nstr: "is_nstrict (cs ! i)" by (auto simp: set_zip)
                hence "(i, cs ! i) \<in> set (zip [0..<?n] cs)" by (force simp: set_zip)
                with init_cs' have "set (index_constraint (i, cs ! i)) \<subseteq> set ics" by force
                hence 
                  "cs ! i \<in> c_of {Equality_Detection_Impl.Ineq i}" 
                  "make_strict (cs ! i) \<in> c_of {TmpSIneq i}" 
                  "make_flipped_ineq (cs ! i) \<in> c_of {FIneq i}" 
                  using nstr unfolding c_of_def by (cases "cs ! i"; force)+
                with c_of_inj 
                have "c_of {Equality_Detection_Impl.Ineq i} = {cs ! i}" 
                  "c_of {TmpSIneq i} = {make_strict (cs ! i)}" 
                  "c_of {FIneq i} = {make_flipped_ineq (cs ! i)}" 
                  by auto
                note nstr this i_n
              } note c_of_ineq = this

              have cIneq: "c_of ?Ineq = ((!) cs) ` set ineq" using c_of_ineq(2) unfolding c_of_def by blast
              have cSIneq: "c_of ?SIneq = (make_strict o (!) cs) ` set ineq" 
                using c_of_ineq(3) unfolding c_of_def o_def by blast

              have "I \<union> ?Ineq = I" using ineq unfolding I_def index_of_def by auto
              with v have "v \<Turnstile>\<^sub>c\<^sub>s (c_of I \<union> c_of ?Ineq)" unfolding c_of_def by auto
              hence v: "v \<Turnstile>\<^sub>c\<^sub>s (c_of I \<union> ((!) cs) ` set ineq)" unfolding cIneq by auto 
              have "Ball (snd ` set ics) is_no_equality" 
                using init_cs[unfolded init_constraints_def Let_def] 
                apply clarsimp
                subgoal for i c j d by (cases d, auto)
                done
              hence no_eq_c: "Ball (c_of I) is_no_equality" for I unfolding c_of_def by auto
              have no_eq_ineq: "i \<in> set ineq \<Longrightarrow> is_no_equality (cs ! i)" for i using c_of_ineq(1)[of i] by (cases "cs ! i", auto)
              define CI where "CI = le_of_constraint ` (c_of I)" 
              from v have v: "\<forall> c \<in> CI \<union> le_of_constraint ` ((!) cs ` set ineq). (v \<Turnstile>\<^sub>l\<^sub>e c)"
                unfolding CI_def 
                by (subst (asm) le_of_constraints, insert no_eq_ineq no_eq_c, auto)
              define p where "p = (\<lambda> i. poly_of_constraint (cs ! i))" 
              define co where "co = (\<lambda> i. const_of_constraint (cs ! i))" 
              have nstri: "Ball ((!) cs ` set ineq) is_nstrict" using c_of_ineq(1) by auto
              have lecs_ineq: "set ine \<subseteq> set ineq \<Longrightarrow> le_of_constraint` ((!) cs ` set ine) = (\<lambda>i. Le_Constraint Leq_Rel (p i) (co i)) ` set ine" for ine
                by (subst poly_const_repr_set, insert nstri, auto simp: p_def co_def)
              from v lecs_ineq[OF subset_refl]
              have v: "\<forall> c \<in> CI \<union> (\<lambda>i. Le_Constraint Leq_Rel (p i) (co i)) ` set ineq. (v \<Turnstile>\<^sub>l\<^sub>e c)" by auto
              have finCI: "finite CI" unfolding CI_def c_of_def by auto
              note main_step = equality_detection_rat[OF finCI finite_set _ _ _ v]
  
              let ?C = "le_of_constraint ` (c_of (set C))" 
              from C have "c_of (set C) \<subseteq> c_of I \<union> c_of ?SIneq" unfolding c_of_def by auto
              hence "c_of (set C) \<subseteq> c_of I \<union> (make_strict o (!) cs) ` set ineq" unfolding cSIneq .
              hence "?C \<subseteq> CI \<union> le_of_constraint ` ((make_strict o (!) cs) ` set ineq)" 
                unfolding CI_def by auto
              also have "le_of_constraint` ((make_strict o (!) cs) ` set ineq) = (\<lambda>i. Le_Constraint Lt_Rel (p i) (co i)) ` set ineq" 
                unfolding o_def unfolding p_def co_def 
                using poly_const_repr_set(2)[OF nstri, unfolded image_comp o_def] by auto
              finally have "?C \<subseteq> CI \<union> (\<lambda>i. Le_Constraint Lt_Rel (p i) (co i)) ` set ineq" by auto

              note main_step = main_step[OF this]

              from unsat[unfolded minimal_unsat_core_def]
              have "\<nexists>v. (set C, v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set ics" by auto
              hence "\<nexists>v. v \<Turnstile>\<^sub>c\<^sub>s c_of (set C)" unfolding c_of_def by auto
              hence "\<nexists>v. \<forall>c\<in>le_of_constraint ` (c_of (set C)). v \<Turnstile>\<^sub>l\<^sub>e c" 
                by (subst (asm) le_of_constraints[OF no_eq_c], auto)

              note main_step = main_step[OF this]

              {
                fix D 
                assume "D \<subset> le_of_constraint ` (c_of (set C))" 
                hence "\<exists> CS. le_of_constraint ` CS = D \<and> CS \<subset> c_of (set C)" 
                  by (metis subset_image_iff subset_not_subset_eq)
                then obtain CS where D: "D = le_of_constraint ` CS" and sub: "CS \<subset> c_of (set C)" by auto
                define c_fun where "c_fun i = (THE x. x \<in> c_of {i})" for i  
                {
                  fix C'
                  assume C': "C' \<subseteq> set C" 
                  {
                    fix i
                    assume "i \<in> C'" 
                    with C' C have "i \<in> I \<union> TmpSIneq ` set ineq" by auto
                    from this[unfolded I_def index_of_def] ineq eq
                    have "i \<in> set (map SIneq sineqs @ map Equality_Detection_Impl.Ineq eqs @ 
                      map FIneq eqs @ map Equality_Detection_Impl.Ineq ineqs @ map FIneq ineqs @ map TmpSIneq ineqs)" (is "_ \<in> ?S")
                      by auto
                    also have "?S \<subseteq> fst ` set ics" using init_constraints(3)[OF init_cs] by auto
                    finally have "i \<in> fst ` set ics" by auto
                    then obtain c where "(i,c) \<in> set ics" by force
                    hence "c \<in> c_of {i}" unfolding c_of_def by force
                    from c_of_inj[OF this] have c: "c_of {i} = {c}" by auto
                    hence "c_fun i = c" unfolding c_fun_def by auto
                    with c have "c_of {i} = {c_fun i}" by auto
                  }
                  hence "c_of C' = c_fun ` C'" unfolding c_of_def by blast
                } note to_c_fun = this
                from sub[unfolded to_c_fun[OF subset_refl]]
                have "CS \<subset> c_fun ` set C" by auto
                hence "\<exists> C'. C' \<subset> set C \<and> CS = c_fun ` C'"
                  by (metis subset_image_iff subset_not_subset_eq)
                then obtain C' where sub: "C' \<subset> set C" and CS: "CS = c_fun ` C'" by auto
                from CS to_c_fun[of C'] sub have CS: "CS = c_of C'" by auto
                from unsat[unfolded minimal_unsat_core_def] dist sub
                have "\<exists>v. (C', v) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set ics"
                  unfolding distinct_indices_def by auto
                hence "\<exists>v. v \<Turnstile>\<^sub>c\<^sub>s CS" unfolding CS c_of_def by auto
                hence "\<exists>v. \<forall>c\<in>D. v \<Turnstile>\<^sub>l\<^sub>e c" unfolding D
                  by (subst (asm) le_of_constraints, unfold CS, insert no_eq_c, auto)
              } 

              note main_step = main_step[OF this]
                               
              {
                fix i e
                assume ieq': "i \<in> set eq'" and mem: "(FIneq i, e) \<in> set ics" 
                from ieq' eq'_def have tmp: "TmpSIneq i \<in> set C" by auto
                have i: "i \<in> set ineq" using ieq' eq'_ineq by auto
                from c_of_ineq(1,3,5)[OF i] tmp
                have *: "make_strict (cs ! i) \<in> c_of (set C)" "is_nstrict (cs ! i)" "i < ?n" 
                  by (auto simp: c_of_def)
                from *(3) have "(i, cs ! i) \<in> set (zip [0..< ?n] cs)" by (force simp: set_zip set_conv_nth)
                hence "set (index_constraint (i, cs ! i)) \<subseteq> set ics" using init_cs[unfolded init_constraints_def Let_def]
                  by force
                hence "(FIneq i, make_flipped_ineq (cs ! i)) \<in> set ics" using *(2) by (cases "cs ! i", auto)
                with mem dist have e: "e = make_flipped_ineq (cs ! i)" by (metis eq_key_imp_eq_value)
                have "le_of_constraint (make_strict (cs ! i)) = Le_Constraint Lt_Rel (p i) (co i)"  
                  by (subst poly_const_repr(2), insert *, auto simp: p_def co_def)
                from this * have "Le_Constraint Lt_Rel (p i) (co i) \<in> le_of_constraint ` (c_of (set C))" 
                  by force
                from main_step[OF _ i this] 
                have eq: "(p i) \<lbrace> v \<rbrace> = co i" by auto
                have id: "le_of_constraint (make_flipped_ineq (cs ! i)) = Le_Constraint Leq_Rel (- p i) (- co i)" 
                  by (subst poly_const_repr(3), insert *, auto simp: p_def co_def)
                from * have "is_no_equality (make_flipped_ineq (cs ! i))" by (cases "cs ! i", auto)
                from le_of_constraint[OF this, of v]
                have "v \<Turnstile>\<^sub>c e" using e id eq by (simp add: valuate_uminus)
              }
              thus "v \<Turnstile>\<^sub>c\<^sub>s c_of (FIneq ` set eq')" unfolding c_of_def by auto
            qed
            finally show ?thesis by simp
          qed
          from equiv equiv_new sol 
          have sol: "(set I', solution_simplex s) \<Turnstile>\<^sub>i\<^sub>c\<^sub>s set ics" unfolding equiv_to_cs_def index_of_def I_def I'_def by auto
          have II': "set I' = set (map FIneq eq') \<union> I" unfolding I'_def I_def index_of_def using eq'_ineq ineq by auto
          let ?ass = "assert_all_simplex (map FIneq eq') s2" 
          {
            fix K
            assume "?ass = Unsat K" 
            from assert_all_simplex_plain_unsat[OF s2 this, folded II'] sol have False by auto
          }
          hence ass: "?ass = Inr s3" unfolding s3_def by (cases ?ass, auto)
          from assert_all_simplex_ok[OF s2 ass]
          have s3: "invariant_simplex ics (set I') s3" unfolding II' by (simp add: ac_simps)
          from s4_def[unfolded ass, simplified] obtain c where 
            "check_simplex s3 = (s4, c)" by (cases "check_simplex s3", auto)
          with check_simplex_plain_unsat[OF s3] sol 
          have "check_simplex s3 = (s4, None)" by (cases c, auto)
          from check_simplex_ok[OF s3 this]
          show "checked_simplex ics (set (index_of ineqs sineqs (eq' @ eq))) s4" unfolding I'_def .
        qed
      qed
    qed
  qed
qed

lemma eq_finder_rat_in_ctxt: "eq_finder_rat = None \<Longrightarrow> \<nexists> v. v \<Turnstile>\<^sub>c\<^sub>s set cs" 
  "eq_finder_rat = Some (eq_idx, v_sol) \<Longrightarrow> {i . i < length cs \<and> is_equality (cs ! i)} \<subseteq> set eq_idx \<and>
     set eq_idx \<subseteq> {0 ..< length cs} \<and>
     distinct eq_idx" (is "_ \<Longrightarrow> ?main1")
  "eq_finder_rat = Some (eq_idx, v_sol) \<Longrightarrow>
     set feq = make_equality ` (!) cs ` set eq_idx \<Longrightarrow>
     set fineq = (!) cs ` ({0 ..< length cs} - set eq_idx) \<Longrightarrow>
     (\<forall> v. v \<Turnstile>\<^sub>c\<^sub>s set cs \<longleftrightarrow> v \<Turnstile>\<^sub>c\<^sub>s (set feq \<union> set fineq)) \<and>
     Ball (set feq) is_equality \<and> Ball (set fineq) is_no_equality \<and>
     (v_sol \<Turnstile>\<^sub>c\<^sub>s (set feq \<union> make_strict ` set fineq))" (is "_ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?main2")
proof -
  assume "eq_finder_rat = None" 
  from this[unfolded eq_finder_rat_def] have "init_eq_finder_rat = None" by (cases init_eq_finder_rat, auto)
  from init_eq_finder_rat(1)[OF this] show "\<nexists> v. v \<Turnstile>\<^sub>c\<^sub>s set cs" .
next
  assume "eq_finder_rat = Some (eq_idx, v_sol)" 
  note res = this[unfolded eq_finder_rat_def] 
  then obtain s ineq sineq eq 
    where init: "init_eq_finder_rat = Some (s, ineq, sineq, eq)" 
    by (cases init_eq_finder_rat, auto)
  from init_eq_finder_rat(2)[OF init] have sineq: "sineq = sineqs"
      and dist: "distinct (ineq @ sineq @ eq)" and set: "set (ineq @ sineq @ eq) = {0..<length cs}" by auto
  note res = res[unfolded init option.simps split sineq]
  from res
  obtain fi fe where main: "eq_finder_main_rat s ineq eq = (fi,fe, v_sol)" 
    by (cases "eq_finder_main_rat s ineq eq", auto)
  note res = res[unfolded main split]
  from res have eq_idx: "eq_idx = fe" 
    by auto
  from dist have dist': "distinct (ineq @ eq)" by auto
  from init_eq_finder_rat(2)[OF init]
  have "checked_simplex ics (set (index_of ineqs sineqs eq)) s" and
    **: "set ineq \<subseteq> set ineqs" "set eqs \<subseteq> set eq \<and> set eq \<union> set ineq = set eqs \<union> set ineqs" 
    "equiv_to_cs eq" 
    and ***: "{0..<length cs} = set (ineq @ sineq @ eq)" "distinct (ineq @ sineq @ eq)" 
    by auto
  from eq_finder_main_rat[OF this(1,2,3) main this(4) dist']
  have *: "set fi \<subseteq> set ineqs" "set eqs \<subseteq> set fe" "set fe \<union> set fi = set eqs \<union> set ineqs"
    and equiv: "equiv_to_cs fe" 
    and sat: "strict_ineq_sat fi fe v_sol"
    and dist'': "distinct (fi @ fe)" by auto

  note init = init_cs[unfolded init_constraints_def Let_def]
  note init' = init_constraints[OF init_cs]
  note eqs = init'(4)

  show ?main1
  proof (intro conjI)
    show "distinct eq_idx" unfolding eq_idx using dist'' by auto
    show "{i . i < length cs \<and> is_equality (cs ! i)} \<subseteq> set eq_idx" 
      unfolding eq_idx using set * ** eqs by auto
    show "set eq_idx \<subseteq> {0..<length cs}" unfolding eq_idx using set * ** by auto
  qed

  assume feq: "set feq = make_equality ` (!) cs ` set eq_idx" 
  assume fineq: "set fineq = (!) cs ` ({0 ..< length cs} - set eq_idx)"
  from feq eq_idx 
  have feq: "set feq = set (map (\<lambda>i. make_equality (cs ! i)) fe)" by auto
  have fineq: "set fineq = set (map ((!) cs) (sineqs @ fi))" 
    unfolding set_map *** using ***(2) unfolding sineq eq_idx fineq
    apply (intro image_cong[OF _ refl])
    unfolding *** sineq using * **(1-2) dist'' by auto
  note ineqs  = init'(5)
  note sineqs = init'(6)
  note ics = init'(7)
  from *(3) have fe: "i \<in> set fe \<Longrightarrow> is_equality (cs ! i) \<or> is_nstrict (cs ! i)" for i
    unfolding eqs ineqs by auto
  let ?n = "length cs" 
  show ?main2
  proof (intro conjI ballI allI)
    define c_of where "c_of I = Simplex.restrict_to I (set ics)" for I  
    have [simp]: "c_of (I \<union> J) = c_of I \<union> c_of J" for I J unfolding c_of_def by auto
    {
      fix v
      have cs: "v \<Turnstile>\<^sub>c\<^sub>s set cs = v \<Turnstile>\<^sub>c\<^sub>s c_of (set (index_of ineqs sineqs fe))" (is "_ = ?cond")
        using equiv[unfolded equiv_to_cs_def] unfolding c_of_def by auto
      have "?cond \<longleftrightarrow> v \<Turnstile>\<^sub>c\<^sub>s c_of (SIneq ` set sineqs) 
      \<and> (v \<Turnstile>\<^sub>c\<^sub>s c_of (Ineq ` set fe)
      \<and> v \<Turnstile>\<^sub>c\<^sub>s c_of (FIneq ` set fe))
      \<and> v \<Turnstile>\<^sub>c\<^sub>s c_of (Ineq ` set ineqs)" unfolding index_of_def
        by auto
      also have "c_of (SIneq ` set sineqs) = ((!) cs) ` set sineqs" 
        unfolding c_of_def ics
        unfolding sineqs by force
      also have "c_of (Ineq ` set ineqs) = ((!) cs) ` set ineqs" 
        unfolding c_of_def ics
        unfolding ineqs eqs 
        by (auto simp: is_nstrict_iff) force
      also have "c_of (FIneq ` set fe) = (\<lambda> i. make_flipped_ineq (cs ! i)) ` set fe" (is "?l = ?r")
      proof 
        show "?l \<subseteq> ?r" 
          unfolding c_of_def ics using fe *(3)
          unfolding ineqs eqs by auto
        show "?r \<subseteq> ?l" 
        proof
          fix c
          assume "c \<in> ?r" 
          then obtain i where i: "i \<in> set fe" and c: "c = make_flipped_ineq (cs ! i)" 
            by auto
          from * i have i': "i \<in> set eqs \<union> set ineqs" by auto
          have "(FIneq i, c) \<in> set ics \<inter> {FIneq i} \<times> UNIV" 
            unfolding c ics using i' by auto
          hence "c \<in> c_of {FIneq i}" unfolding c_of_def by force
          with i show "c \<in> ?l" unfolding c_of_def by auto
        qed
      qed
      also have "c_of (Ineq ` set fe) = (\<lambda> i. make_ineq (cs ! i)) ` set fe" (is "?l = ?r")
      proof 
        {
          fix i
          have "i \<in> set fe \<Longrightarrow> is_nstrict (cs ! i) \<Longrightarrow> cs ! i \<in> (\<lambda>i. make_ineq (cs ! i)) ` set fe" 
            by (cases "cs ! i"; force)
        }
        thus "?l \<subseteq> ?r" 
          unfolding c_of_def ics using fe *(3)
          unfolding ineqs eqs by auto
        show "?r \<subseteq> ?l" 
        proof
          fix c
          assume "c \<in> ?r" 
          then obtain i where i: "i \<in> set fe" and c: "c = make_ineq (cs ! i)" 
            by auto
          from * i have i': "i \<in> set eqs \<union> set ineqs" by auto
          from fe[OF i]
          have "(Ineq i, c) \<in> set ics \<inter> {Ineq i} \<times> UNIV" 
          proof 
            assume "is_equality (cs ! i)" 
            with i' have "i \<in> set eqs" unfolding ineqs by (cases "cs ! i", auto)
            thus ?thesis 
              unfolding c ics using i' by (cases "cs ! i"; force)
          next
            assume stri: "is_nstrict (cs ! i)" 
            with i' have i': "i \<in> set ineqs" unfolding eqs by (cases "cs ! i", auto)
            from stri have c: "c = cs ! i" unfolding c by (cases "cs ! i", auto)
            thus ?thesis 
              unfolding c ics using i' by (cases "cs ! i"; force)
          qed
          hence "c \<in> c_of {Ineq i}" unfolding c_of_def by force
          with i show "c \<in> ?l" unfolding c_of_def by auto
        qed
      qed
      also have "v \<Turnstile>\<^sub>c\<^sub>s ((\<lambda>i. make_ineq (cs ! i)) ` set fe) \<and>
      v \<Turnstile>\<^sub>c\<^sub>s ((\<lambda>i. make_flipped_ineq (cs ! i)) ` set fe)
      \<longleftrightarrow> v \<Turnstile>\<^sub>c\<^sub>s ((\<lambda> i. make_equality (cs ! i)) ` set fe)" (is "?l = ?r")
      proof -
        have "?l \<longleftrightarrow> (\<forall> i \<in> set fe. v \<Turnstile>\<^sub>c make_ineq (cs ! i) \<and> v \<Turnstile>\<^sub>c make_flipped_ineq (cs ! i))" 
          by auto
        also have "\<dots> \<longleftrightarrow> (\<forall> i \<in> set fe. v \<Turnstile>\<^sub>c make_equality (cs ! i))" 
          apply (intro ball_cong[OF refl])
          subgoal for i using fe[of i]
            by (cases "cs ! i", auto)
          done
        also have "\<dots> \<longleftrightarrow> ?r" by auto
        finally show "?l = ?r" .
      qed
      finally have "?cond \<longleftrightarrow>
        v \<Turnstile>\<^sub>c\<^sub>s ((!) cs ` (set sineqs \<union> set ineqs) \<union> (\<lambda>i. make_equality (cs ! i)) ` set fe)" 
        by auto
      also have "\<dots> \<longleftrightarrow> v \<Turnstile>\<^sub>c\<^sub>s (set feq \<union> set fineq)" (is "?l = ?r")
      proof
        show "?l \<Longrightarrow> ?r" unfolding feq fineq using * by auto
        assume v: ?r
        show ?l
        proof
          fix c 
          assume c: "c \<in> (!) cs ` (set sineqs \<union> set ineqs) \<union>
             (\<lambda>i. make_equality (cs ! i)) ` set fe" 
          show "v \<Turnstile>\<^sub>c c" 
          proof (cases "c \<in> (!) cs ` (set sineqs \<union> set fi) \<union>
             (\<lambda>i. make_equality (cs ! i)) ` set fe") 
            case True
            thus ?thesis using v feq fineq * by auto
          next
            case False
            with c obtain i where "i \<in> set ineqs - set fi" and c: "c = cs ! i" by auto
            with * have i: "i \<in> set fe" by auto
            with v have "v \<Turnstile>\<^sub>c make_equality (cs ! i)" 
              using v feq fineq * by auto
            with fe[OF i] show ?thesis unfolding c by (cases "cs ! i", auto)
          qed
        qed
      qed
      finally have main: "?cond \<longleftrightarrow> v \<Turnstile>\<^sub>c\<^sub>s (set feq \<union> set fineq)" by auto
      with cs show "v \<Turnstile>\<^sub>c\<^sub>s set cs = v \<Turnstile>\<^sub>c\<^sub>s (set feq \<union> set fineq)" by auto
      note main
    } note main = this 
    fix c
    {
      assume "c \<in> set feq" 
      from this[unfolded feq] obtain i where i: "i \<in> set fe" 
        and c: "c = make_equality (cs ! i)" by auto
      from i * have "i \<in> set eqs \<union> set ineqs" by auto
      hence "is_equality (cs ! i) \<or> is_nstrict (cs ! i)" 
        unfolding ineqs eqs by auto
      thus "is_equality c" unfolding c
        by (cases "cs ! i", auto)
    }  
    {
      assume "c \<in> set fineq" 
      from this[unfolded fineq] * obtain i where i: "i \<in> set sineqs \<union> set ineqs" 
        and c: "c = cs ! i" by auto
      hence "is_nstrict c \<or> is_strict c" unfolding c sineqs ineqs by auto
      thus "is_no_equality c" by (cases c, auto)
    }
    from sat[unfolded strict_ineq_sat_def] 
    have old: "v_sol \<Turnstile>\<^sub>c\<^sub>s c_of (set (index_of ineqs sineqs fe))" and new: "v_sol \<Turnstile>\<^sub>c\<^sub>s c_of (TmpSIneq ` set fi)" 
      by (auto simp: c_of_def)
    have tmp: "c_of (TmpSIneq ` set fi) = (\<lambda> i. make_strict (cs ! i)) ` set fi" 
      apply (rule sym)
      unfolding c_of_def ics using *(1) unfolding ineqs 
      by force

    fix c
    assume "c \<in> set feq \<union> make_strict ` set fineq"
    thus "v_sol \<Turnstile>\<^sub>c c" 
    proof
      assume "c \<in> set feq" 
      thus ?thesis using old[unfolded main] by auto
    next
      assume "c \<in> make_strict ` set fineq" 
      from this[unfolded fineq]
      obtain i where i: "i \<in> set sineqs \<or> i \<in> set fi" 
        and c: "c = make_strict (cs ! i)" by force
      from i show ?thesis 
      proof
        assume "i \<in> set fi" 
        with new[unfolded tmp] c show ?thesis by auto
      next
        assume i: "i \<in> set sineqs" 
        hence v: "v_sol \<Turnstile>\<^sub>c (cs ! i)" using old[unfolded main]
          unfolding fineq by auto
        from i[unfolded sineqs] have "make_strict (cs ! i) = cs ! i" 
          by (cases "cs ! i", auto)
        with v show ?thesis unfolding c by auto
      qed
    qed
  qed
qed


end
end


lemma eq_finder_rat: 
  "eq_finder_rat cs = None \<Longrightarrow> \<nexists>v. v \<Turnstile>\<^sub>c\<^sub>s set cs" (is "?p1 \<Longrightarrow> ?g1")
  "eq_finder_rat cs = Some (eq_idx, v_sol) \<Longrightarrow> 
    {i . i < length cs \<and> is_equality (cs ! i)} \<subseteq> set eq_idx \<and>
    set eq_idx \<subseteq> {0 ..< length cs} \<and>
    distinct eq_idx" (is "?p2 \<Longrightarrow> ?g2")
  "eq_finder_rat cs = Some (eq_idx, v_sol) \<Longrightarrow>
   set eq = make_equality ` (!) cs ` set eq_idx \<Longrightarrow>
   set ineq = (!) cs ` ({0 ..< length cs} - set eq_idx) \<Longrightarrow>
    (\<forall>v. v \<Turnstile>\<^sub>c\<^sub>s set cs \<longleftrightarrow> v \<Turnstile>\<^sub>c\<^sub>s (set eq \<union> set ineq)) \<and>
    Ball (set eq) is_equality \<and> Ball (set ineq) is_no_equality \<and>
    (v_sol \<Turnstile>\<^sub>c\<^sub>s (set eq \<union> make_strict ` set ineq))" 
    (is "?p2 \<Longrightarrow> ?p3 \<Longrightarrow> ?p4 \<Longrightarrow> ?g3")
proof -
  obtain ics ineqs sineqs eqs
    where "init_constraints cs = (ics, ineqs, sineqs, eqs)" 
    by (cases "init_constraints cs")
  from eq_finder_rat_in_ctxt[OF this]
  show "?p1 \<Longrightarrow> ?g1" "?p2 \<Longrightarrow> ?g2" "?p2 \<Longrightarrow> ?p3 \<Longrightarrow> ?p4 \<Longrightarrow> ?g3" by auto
qed

hide_fact eq_finder_rat_in_ctxt

end
