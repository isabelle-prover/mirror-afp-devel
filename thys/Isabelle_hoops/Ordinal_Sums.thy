section\<open>Ordinal sums\<close>

text\<open>We define @{text "tower of hoops"}, a family of almost disjoint hoops indexed by a total order.
 This is based on the definition of @{text "bounded tower of irreducible hoops"} in \<^cite>\<open>"BUSANICHE2005"\<close>
 (see paragraph after Lemma 3.3). Parting from a tower of hoops we can define a hoop known as @{text "ordinal sum"}.
 Ordinal sums are a fundamental tool in the study of totally ordered hoops.\<close>

theory Ordinal_Sums
  imports Hoops 
begin

subsection\<open>Tower of hoops\<close>

locale tower_of_hoops =
  fixes index_set :: "'b set" ("I")
  fixes index_lesseq :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<le>\<^sup>I" 60)
  fixes index_less :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "<\<^sup>I" 60)
  fixes universes :: "'b \<Rightarrow> ('a set)" ("UNI")
  fixes multiplications :: "'b \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a)" ("MUL")
  fixes implications :: "'b \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a)" ("IMP")
  fixes sum_one :: 'a ("1\<^sup>S")
  assumes index_set_total_order: "total_poset_on I (\<le>\<^sup>I) (<\<^sup>I)"
  and almost_disjoint: "i \<in> I \<Longrightarrow> j \<in> I \<Longrightarrow> i \<noteq> j \<Longrightarrow> UNI i \<inter> UNI j = {1\<^sup>S}"
  and family_of_hoops: "i \<in> I \<Longrightarrow> hoop (UNI i) (MUL i) (IMP i) 1\<^sup>S"
begin

sublocale total_poset_on "I" "(\<le>\<^sup>I)" "(<\<^sup>I)"
  using index_set_total_order by simp                   

abbreviation (uni_i)
  uni_i :: "['b] \<Rightarrow> ('a set)" ("(\<bbbA>(\<^sub>_))" [61] 60)
  where "\<bbbA>\<^sub>i \<equiv> UNI i"

abbreviation (mult_i)
  mult_i :: "['b] \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a)" ("(*(\<^sup>_))" [61] 60)
  where "*\<^sup>i \<equiv> MUL i"

abbreviation (imp_i)
  imp_i :: "['b] \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a)" ("(\<rightarrow>(\<^sup>_))" [61] 60)
  where "\<rightarrow>\<^sup>i \<equiv> IMP i"

abbreviation (mult_i_xy)
  mult_i_xy :: "['a, 'b, 'a] \<Rightarrow> 'a"  ("((_)/ *(\<^sup>_) / (_))" [61, 50, 61] 60)
  where "x *\<^sup>i y \<equiv> MUL i x y"

abbreviation (imp_i_xy)
  imp_i_xy :: "['a, 'b, 'a] \<Rightarrow> 'a"  ("((_)/ \<rightarrow>(\<^sup>_) / (_))" [61, 50, 61] 60)
  where "x \<rightarrow>\<^sup>i y \<equiv> IMP i x y"

subsection\<open>Ordinal sum universe\<close>

definition sum_univ :: "'a set" ("S")
  where "S = {x. \<exists> i \<in> I. x \<in> \<bbbA>\<^sub>i}"

lemma sum_one_closed [simp]: "1\<^sup>S \<in> S"
  using family_of_hoops hoop.one_closed not_empty sum_univ_def by fastforce

lemma sum_subsets: 
  assumes "i \<in> I"
  shows "\<bbbA>\<^sub>i \<subseteq> S"
  using sum_univ_def assms by blast

subsection\<open>Floor function: definition and properties\<close>

lemma floor_unique:
  assumes "a \<in> S-{1\<^sup>S}"
  shows "\<exists>! i. i \<in> I \<and> a \<in> \<bbbA>\<^sub>i"
  using assms sum_univ_def almost_disjoint by blast

function floor :: "'a \<Rightarrow> 'b" where
  "floor x = (THE i. i \<in> I \<and> x \<in> \<bbbA>\<^sub>i)" if "x \<in> S-{1\<^sup>S}"
| "floor x = undefined" if "x = 1\<^sup>S \<or> x \<notin> S"
  by auto
termination by lexicographic_order

abbreviation (uni_floor)
  uni_floor :: "['a] \<Rightarrow> ('a set)" ("(\<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r (\<^sub>_))" [61] 60)
  where "\<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>x \<equiv> UNI (floor x)"

abbreviation (mult_floor)
  mult_floor :: "['a] \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a)"  ("(*\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r (\<^sup>_))" [61] 60)
  where "*\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a \<equiv> MUL (floor a)"

abbreviation (imp_floor)
  imp_floor :: "['a] \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a)"  ("(\<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r (\<^sup>_))" [61] 60)
  where "\<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a \<equiv> IMP (floor a)"

abbreviation (mult_floor_xy)
  mult_floor_xy :: "['a, 'a, 'a] \<Rightarrow> 'a"  ("((_)/ *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r (\<^sup>_) / (_))" [61, 50, 61] 60)
  where "x *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>y z \<equiv> MUL (floor y) x z"

abbreviation (imp_floor_xy)
  imp_floor_xy :: "['a, 'a, 'a] \<Rightarrow> 'a"  ("((_)/ \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r (\<^sup>_) / (_))" [61, 50, 61] 60)
  where "x \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>y z \<equiv> IMP (floor y) x z"

lemma floor_prop:
  assumes "a \<in> S-{1\<^sup>S}"
  shows "floor a \<in> I \<and> a \<in> \<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a"
proof -
  have "floor a = (THE i. i \<in> I \<and> a \<in> \<bbbA>\<^sub>i)"
    using assms by auto
  then
  show ?thesis
    using assms theI_unique floor_unique by (metis (mono_tags, lifting))
qed

lemma floor_one_closed:
  assumes "i \<in> I"
  shows "1\<^sup>S \<in> \<bbbA>\<^sub>i"
  using assms floor_prop family_of_hoops hoop.one_closed by metis

lemma floor_mult_closed:
  assumes "i \<in> I" "a \<in> \<bbbA>\<^sub>i" "b \<in> \<bbbA>\<^sub>i" 
  shows "a *\<^sup>i b \<in> \<bbbA>\<^sub>i"
  using assms family_of_hoops hoop.mult_closed by meson

lemma floor_imp_closed:
  assumes "i \<in> I" "a \<in> \<bbbA>\<^sub>i" "b \<in> \<bbbA>\<^sub>i" 
  shows "a \<rightarrow>\<^sup>i b \<in> \<bbbA>\<^sub>i"
  using assms family_of_hoops hoop.imp_closed by meson

subsection\<open>Ordinal sum multiplication and implication\<close>

function sum_mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "*\<^sup>S" 60) where
  "x *\<^sup>S y = x *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>x y" if  "x \<in> S-{1\<^sup>S}" "y \<in> S-{1\<^sup>S}" "floor x = floor y"
| "x *\<^sup>S y = x" if "x \<in> S-{1\<^sup>S}" "y \<in> S-{1\<^sup>S}" "floor x <\<^sup>I floor y"
| "x *\<^sup>S y = y" if "x \<in> S-{1\<^sup>S}" "y \<in> S-{1\<^sup>S}" "floor y <\<^sup>I floor x"
| "x *\<^sup>S y = y" if "x = 1\<^sup>S" "y \<in> S-{1\<^sup>S}"
| "x *\<^sup>S y = x" if "x \<in> S-{1\<^sup>S}" "y = 1\<^sup>S"
| "x *\<^sup>S y = 1\<^sup>S" if "x = 1\<^sup>S" "y = 1\<^sup>S"
| "x *\<^sup>S y = undefined" if "x \<notin> S \<or> y \<notin> S"
  apply auto
  using floor.cases floor.simps(1) floor_prop trichotomy apply smt
  using floor_prop strict_iff_order apply force
  using floor_prop strict_iff_order apply force
  using floor_prop trichotomy by auto
termination by lexicographic_order

function sum_imp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<rightarrow>\<^sup>S" 60) where
  "x \<rightarrow>\<^sup>S y = x \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>x y" if "x \<in> S-{1\<^sup>S}" "y \<in> S-{1\<^sup>S}" "floor x = floor y"
| "x \<rightarrow>\<^sup>S y = 1\<^sup>S" if "x \<in> S-{1\<^sup>S}" "y \<in> S-{1\<^sup>S}" "floor x <\<^sup>I floor y"
| "x \<rightarrow>\<^sup>S y = y" if "x \<in> S-{1\<^sup>S}" "y \<in> S-{1\<^sup>S}" "floor y <\<^sup>I floor x"
| "x \<rightarrow>\<^sup>S y = y" if "x = 1\<^sup>S" "y \<in> S-{1\<^sup>S}"
| "x \<rightarrow>\<^sup>S y = 1\<^sup>S" if "x \<in> S-{1\<^sup>S}" "y = 1\<^sup>S"
| "x \<rightarrow>\<^sup>S y = 1\<^sup>S" if "x = 1\<^sup>S" "y = 1\<^sup>S"
| "x \<rightarrow>\<^sup>S y = undefined" if "x \<notin> S \<or> y \<notin> S"
  apply auto
  using floor.cases floor.simps(1) floor_prop trichotomy apply smt
  using floor_prop strict_iff_order apply force
  using floor_prop strict_iff_order apply force
  using floor_prop trichotomy by auto
termination by lexicographic_order

subsubsection\<open>Some multiplication properties\<close>

lemma sum_mult_not_one_aux:
  assumes "a \<in> S-{1\<^sup>S}" "b \<in> \<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a"
  shows "a *\<^sup>S b \<in> (\<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a)-{1\<^sup>S}"
proof -
  consider (1) "b \<in> S-{1\<^sup>S}"
    | (2) "b = 1\<^sup>S"
    using sum_subsets assms floor_prop by blast
  then
  show ?thesis
  proof(cases)
    case 1
    then
    have same_floor: "floor a = floor b"
      using assms floor_prop floor_unique by metis
    moreover
    have "a *\<^sup>S b = a *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a b"
      using "1" assms(1) same_floor by simp
    moreover
    have "a \<in> (\<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a)-{1\<^sup>S} \<and> b \<in> (\<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a)-{1\<^sup>S}"
      using "1" assms floor_prop by simp
    ultimately
    show ?thesis
      using assms(1) family_of_hoops floor_prop hoop.mult_C by metis
  next
    case 2
    then
    show ?thesis
      using assms(1) floor_prop by auto
  qed
qed

corollary sum_mult_not_one:
  assumes "a \<in> S-{1\<^sup>S}" "b \<in> \<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a"
  shows "a *\<^sup>S b \<in> S-{1\<^sup>S} \<and> floor (a *\<^sup>S b) = floor a"
proof -
  have "a *\<^sup>S b \<in> (\<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a)-{1\<^sup>S}"
    using sum_mult_not_one_aux assms by meson
  then 
  have "a *\<^sup>S b \<in> S-{1\<^sup>S} \<and> a *\<^sup>S b \<in> \<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a"
    using sum_subsets assms(1) floor_prop by fastforce
  then
  show ?thesis
    using assms(1) floor_prop floor_unique by metis
qed
   
lemma sum_mult_A: 
  assumes "a \<in> S-{1\<^sup>S}" "b \<in> \<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a"
  shows "a *\<^sup>S b = a *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a b  \<and> b *\<^sup>S a = b *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a a"
proof -
  consider (1) "b \<in> S-{1\<^sup>S}"
    | (2) "b = 1\<^sup>S"
    using sum_subsets assms floor_prop by blast
  then
  show ?thesis
  proof(cases)
    case 1
    then
    have "floor a = floor b"
      using assms floor.cases floor_prop floor_unique by metis
    then
    show ?thesis
      using "1" assms by auto
  next
    case 2
    then
    show ?thesis
      using assms(1) family_of_hoops floor_prop hoop.mult_neutr hoop.mult_neutr_2
      by fastforce
  qed
qed

subsubsection\<open>Some implication properties\<close>

lemma sum_imp_floor:
  assumes "a \<in> S-{1\<^sup>S}" "b \<in> S-{1\<^sup>S}" "floor a = floor b" "a \<rightarrow>\<^sup>S b \<in> S-{1\<^sup>S}" 
  shows "floor (a \<rightarrow>\<^sup>S b) = floor a"
proof -
  have "a \<rightarrow>\<^sup>S b \<in> \<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a"
    using sum_imp.simps(1) assms(1-3) floor_imp_closed floor_prop
    by metis
  then 
  show ?thesis
    using assms(1,4) floor_prop floor_unique by blast
qed

lemma sum_imp_A:
  assumes "a \<in> S-{1\<^sup>S}" "b \<in> \<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a"
  shows "a \<rightarrow>\<^sup>S b = a \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a b"
proof -
  consider (1) "b \<in> S-{1\<^sup>S}"
    | (2) "b = 1\<^sup>S"
    using sum_subsets assms floor_prop by blast
  then
  show ?thesis
  proof(cases)
    case 1
    then 
    show ?thesis
      using sum_imp.simps(1) assms floor_prop floor_unique by metis
  next
    case 2
    then
    show ?thesis
      using sum_imp.simps(5) assms(1) family_of_hoops floor_prop
            hoop.imp_one_top
      by metis
  qed
qed

lemma sum_imp_B:
  assumes "a \<in> S-{1\<^sup>S}" "b \<in> \<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a"
  shows "b \<rightarrow>\<^sup>S a = b \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a a"
proof -
  consider (1) "b \<in> S-{1\<^sup>S}"
    | (2) "b = 1\<^sup>S"
    using sum_subsets assms floor_prop by blast
  then
  show ?thesis
  proof(cases)
    case 1
    then 
    show ?thesis
      using sum_imp.simps(1) assms floor_prop floor_unique by metis
  next
    case 2
    then
    show ?thesis
      using sum_imp.simps(4) assms(1) family_of_hoops floor_prop
            hoop.imp_one_C
      by metis
  qed
qed

lemma sum_imp_floor_antisymm:
  assumes "a \<in> S-{1\<^sup>S}" "b \<in> S-{1\<^sup>S}" "floor a = floor b"
          "a \<rightarrow>\<^sup>S b = 1\<^sup>S" "b \<rightarrow>\<^sup>S a = 1\<^sup>S"
  shows "a = b"
proof -
  have "a \<in> \<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a \<and> b \<in> \<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a \<and> floor a \<in> I"
    using floor_prop assms by metis
  moreover 
  have "a \<rightarrow>\<^sup>S b = a \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a b \<and> b \<rightarrow>\<^sup>S a = b \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a a"
    using assms by auto
  ultimately
  show ?thesis
    using assms(4,5) family_of_hoops hoop.ord_antisymm_equiv by metis
qed

corollary sum_imp_C:
  assumes "a \<in> S-{1\<^sup>S}" "b \<in> S-{1\<^sup>S}" "a \<noteq> b" "floor a = floor b" "a \<rightarrow>\<^sup>S b = 1\<^sup>S"
  shows "b \<rightarrow>\<^sup>S a \<noteq> 1\<^sup>S"
  using sum_imp_floor_antisymm assms by blast

lemma sum_imp_D:
  assumes "a \<in> S"
  shows "1\<^sup>S \<rightarrow>\<^sup>S a = a"
  using sum_imp.simps(4,6) assms by blast

lemma sum_imp_E:
  assumes "a \<in> S"
  shows "a \<rightarrow>\<^sup>S 1\<^sup>S = 1\<^sup>S"
  using sum_imp.simps(5,6) assms by blast

subsection\<open>The ordinal sum of a tower of hoops is a hoop\<close>

subsubsection\<open>@{term S} is not empty\<close>

lemma sum_not_empty: "S \<noteq> \<emptyset>"
  using sum_one_closed by blast

subsubsection\<open>@{term sum_mult} and @{term sum_imp} are well defined\<close>

lemma sum_mult_closed_one: 
  assumes "a \<in> S" "b \<in> S" "a = 1\<^sup>S \<or> b = 1\<^sup>S"
  shows "a *\<^sup>S b \<in> S"
  using sum_mult.simps(4-6) assms floor.cases by metis

lemma sum_mult_closed_not_one:
  assumes "a \<in> S-{1\<^sup>S}" "b \<in> S-{1\<^sup>S}"
  shows "a *\<^sup>S b \<in> S-{1\<^sup>S}"
proof -
  from assms
  consider (1) "floor a = floor b"
    | (2) "floor a <\<^sup>I floor b \<or> floor b <\<^sup>I floor a"
    using trichotomy floor_prop by blast
  then
  show ?thesis
  proof(cases)
    case 1 
    then 
    show ?thesis
      using sum_mult_not_one assms floor_prop by metis
  next 
    case 2
    then
    show ?thesis
      using assms by auto
  qed
qed

lemma sum_mult_closed:
  assumes "a \<in> S" "b \<in> S"
  shows "a *\<^sup>S b \<in> S"
  using sum_mult_closed_not_one sum_mult_closed_one assms by auto

lemma sum_imp_closed_one:
  assumes "a \<in> S" "b \<in> S" "a = 1\<^sup>S \<or> b = 1\<^sup>S"
  shows "a \<rightarrow>\<^sup>S b \<in> S"
  using sum_imp.simps(4-6) assms floor.cases by metis

lemma sum_imp_closed_not_one:
  assumes "a \<in> S-{1\<^sup>S}" "b \<in> S-{1\<^sup>S}"
  shows "a \<rightarrow>\<^sup>S b \<in> S"
proof -
  from assms
  consider (1) "floor a = floor b"
    | (2) "floor a <\<^sup>I floor b \<or> floor b <\<^sup>I floor a"
    using trichotomy floor_prop by blast
  then
  show "a \<rightarrow>\<^sup>S b \<in> S"
  proof(cases)
    case 1 
    then
    have "a \<rightarrow>\<^sup>S b = a \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a b" 
      using assms by auto
    moreover
    have "a \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a b \<in> \<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a"
      using "1" assms floor_imp_closed floor_prop by metis
    ultimately
    show ?thesis
      using sum_subsets assms(1) floor_prop by auto
  next
    case 2
    then
    show ?thesis
      using assms by auto
  qed
qed

lemma sum_imp_closed:
  assumes "a \<in> S" "b \<in> S"
  shows "a \<rightarrow>\<^sup>S b \<in> S"
  using sum_imp_closed_one sum_imp_closed_not_one assms by auto

subsubsection\<open>Neutrality of @{term sum_one}\<close>

lemma sum_mult_neutr:
  assumes "a \<in> S"
  shows "a *\<^sup>S 1\<^sup>S = a \<and> 1\<^sup>S *\<^sup>S a = a"
  using assms sum_mult.simps(4-6) by blast

subsubsection\<open>Commutativity of @{term sum_mult}\<close>

text\<open>Now we prove @{term "x *\<^sup>S y = y *\<^sup>S x"} by showing
that it holds when one of the variables is equal to @{term "1\<^sup>S"}. Then
we consider when none of them is @{term "1\<^sup>S"}.\<close>

lemma sum_mult_comm_one: 
  assumes "a \<in> S" "b \<in> S" "a = 1\<^sup>S \<or> b = 1\<^sup>S" 
  shows "a *\<^sup>S b = b *\<^sup>S a"
  using sum_mult_neutr assms by auto

lemma sum_mult_comm_not_one: 
  assumes "a \<in> S-{1\<^sup>S}" "b \<in> S-{1\<^sup>S}"
  shows "a *\<^sup>S b = b *\<^sup>S a"
proof -
  from assms
  consider (1) "floor a = floor b"
    | (2) "floor a <\<^sup>I floor b \<or> floor b <\<^sup>I floor a"
    using trichotomy floor_prop by blast
  then
  show ?thesis
  proof(cases)
    case 1
    then 
    have same_floor: "b \<in> \<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a"
      using assms(2) floor_prop by simp
    then
    have "a *\<^sup>S b = a *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a b"
      using sum_mult_A assms(1) by blast
    also
    have "\<dots> = b *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a a"
      using assms(1) family_of_hoops floor_prop hoop.mult_comm same_floor
      by meson
    also
    have "\<dots> = b *\<^sup>S a"
      using sum_mult_A assms(1) same_floor by simp
    finally 
    show ?thesis
      by auto
  next
    case 2
    then
    show ?thesis
      using assms by auto
  qed
qed

lemma sum_mult_comm:
  assumes "a \<in> S" "b \<in> S"
  shows "a *\<^sup>S b = b *\<^sup>S a"
  using assms sum_mult_comm_one sum_mult_comm_not_one by auto

subsubsection\<open>Associativity of @{term sum_mult}\<close>

text\<open>Next we prove @{term "x *\<^sup>S (y *\<^sup>S z) = (x *\<^sup>S y) *\<^sup>S z"}.\<close>

lemma sum_mult_assoc_one:
  assumes "a \<in> S" "b \<in> S" "c \<in> S" "a = 1\<^sup>S \<or> b = 1\<^sup>S \<or> c = 1\<^sup>S"
  shows "a *\<^sup>S (b *\<^sup>S c) = (a *\<^sup>S b) *\<^sup>S c" 
  using  sum_mult_neutr assms sum_mult_closed by metis

lemma sum_mult_assoc_not_one:
  assumes "a \<in> S-{1\<^sup>S}" "b \<in> S-{1\<^sup>S}" "c \<in> S-{1\<^sup>S}"
  shows "a *\<^sup>S (b *\<^sup>S c) = (a *\<^sup>S b) *\<^sup>S c"
proof -
  from assms
  consider (1) "floor a = floor b" "floor b = floor c"
    | (2) "floor a = floor b" "floor b <\<^sup>I floor c"
    | (3) "floor a = floor b" "floor c <\<^sup>I floor b"
    | (4) "floor a <\<^sup>I floor b" "floor b = floor c"
    | (5) "floor a <\<^sup>I floor b" "floor b <\<^sup>I floor c"
    | (6) "floor a <\<^sup>I floor b" "floor c <\<^sup>I floor b"
    | (7) "floor b <\<^sup>I floor a" "floor b = floor c"
    | (8) "floor b <\<^sup>I floor a" "floor b <\<^sup>I floor c"
    | (9) "floor b <\<^sup>I floor a" "floor c <\<^sup>I floor b"
     using trichotomy floor_prop by meson
  then
  show ?thesis
  proof(cases)
    case 1
    then
    have "a *\<^sup>S (b *\<^sup>S c) = a *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a (b *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a c)"
      using sum_mult_A assms floor_mult_closed floor_prop by metis
    also
    have "\<dots> = (a *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a b) *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a c"
      using "1" assms family_of_hoops floor_prop hoop.mult_assoc by metis
    also 
    have "\<dots> = (a *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>b b) *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>b c"
      using "1" by simp
    also
    have "\<dots> = (a *\<^sup>S b) *\<^sup>S c"
      using "1" sum_mult_A assms floor_mult_closed floor_prop by metis
    finally
    show ?thesis 
      by auto
  next
    case 2 
    then
    show ?thesis
      using sum_mult.simps(2,3) sum_mult_not_one assms floor_prop by metis
  next
    case 3
    then
    show ?thesis
      using sum_mult.simps(3) sum_mult_not_one assms floor_prop by metis
  next
    case 4
    then
    show ?thesis
      using sum_mult.simps(2) sum_mult_not_one assms floor_prop by metis
  next
    case 5
    then
    show ?thesis
      using sum_mult.simps(2) assms floor_prop strict_trans by metis
  next
    case 6
    then
    show ?thesis
      using sum_mult.simps(2,3) assms by metis
  next
    case 7
    then
    show ?thesis
      using sum_mult.simps(3) sum_mult_not_one assms floor_prop by metis
  next
    case 8
    then
    show ?thesis
      using sum_mult.simps(2,3) assms by metis
  next
    case 9
    then 
    show ?thesis
      using sum_mult.simps(3) assms floor_prop strict_trans by metis
  qed
qed

lemma sum_mult_assoc:
  assumes "a \<in> S" "b \<in> S" "c \<in> S"
  shows "a *\<^sup>S (b *\<^sup>S c) = (a *\<^sup>S b) *\<^sup>S c"
  using assms sum_mult_assoc_one sum_mult_assoc_not_one by blast

subsubsection\<open>Reflexivity of @{term sum_imp}\<close>

lemma sum_imp_reflex:
  assumes "a \<in> S"
  shows "a \<rightarrow>\<^sup>S a = 1\<^sup>S"
proof -
  consider (1) "a \<in> S-{1\<^sup>S}"
    | (2) "a = 1\<^sup>S"
    using assms by blast
  then
  show ?thesis
  proof(cases)
    case 1
    then 
    have "a \<rightarrow>\<^sup>S a = a \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a a"
      by simp
    then
    show ?thesis
      using "1" family_of_hoops floor_prop hoop.imp_reflex by metis
  next
    case 2
    then 
    show ?thesis
      by simp
  qed
qed

subsubsection\<open>Divisibility\<close>

text\<open>We prove @{term "x *\<^sup>S (x \<rightarrow>\<^sup>S y) = y *\<^sup>S (y \<rightarrow>\<^sup>S x)"} using the same methods as before.\<close>

lemma sum_divisibility_one:
  assumes "a \<in> S" "b \<in> S" "a = 1\<^sup>S \<or> b = 1\<^sup>S"
  shows  "a *\<^sup>S (a \<rightarrow>\<^sup>S b) = b *\<^sup>S (b \<rightarrow>\<^sup>S a)"
proof -
  have "x \<rightarrow>\<^sup>S y = y \<and> y \<rightarrow>\<^sup>S x = 1\<^sup>S" if "x = 1\<^sup>S" "y \<in> S" for x y
    using sum_imp_D sum_imp_E that by simp
  then
  show ?thesis
    using assms sum_mult_neutr by metis
qed

lemma sum_divisibility_aux:
  assumes "a \<in> S-{1\<^sup>S}" "b \<in> \<bbbA>\<^sub>f\<^sub>l\<^sub>o\<^sub>o\<^sub>r \<^sub>a"
  shows "a *\<^sup>S (a \<rightarrow>\<^sup>S b) = a *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a (a \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a b)"
  using sum_imp_A sum_mult_A assms floor_imp_closed floor_prop by metis

lemma sum_divisibility_not_one:
  assumes "a \<in> S-{1\<^sup>S}" "b \<in> S-{1\<^sup>S}"
  shows "a *\<^sup>S (a \<rightarrow>\<^sup>S b) = b *\<^sup>S (b \<rightarrow>\<^sup>S a)"
proof -
  from assms
  consider (1) "floor a = floor b"
    | (2) "floor a <\<^sup>I floor b \<or> floor b <\<^sup>I floor a"
    using trichotomy floor_prop by blast
  then
  show ?thesis
  proof(cases)
    case 1
    then
    have "a *\<^sup>S (a \<rightarrow>\<^sup>S b) =  a *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a (a \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a b)"
      using "1" sum_divisibility_aux assms floor_prop by metis
    also
    have "\<dots> = b *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a (b \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a a)"
      using "1" assms family_of_hoops floor_prop hoop.divisibility by metis
    also
    have "\<dots> = b *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>b (b \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>b a)"
      using "1" by simp
    also
    have "\<dots> = b *\<^sup>S (b \<rightarrow>\<^sup>S a)"
      using "1" sum_divisibility_aux assms floor_prop by metis
    finally
    show ?thesis
      by auto
  next 
    case 2
    then
    show ?thesis
      using assms by auto
  qed
qed

lemma sum_divisibility:
  assumes "a \<in> S" "b \<in> S"
  shows "a *\<^sup>S (a \<rightarrow>\<^sup>S b) = b *\<^sup>S (b \<rightarrow>\<^sup>S a)"
  using assms sum_divisibility_one sum_divisibility_not_one by auto

subsubsection\<open>Residuation\<close>

text\<open>Finally we prove @{term "(x *\<^sup>S y) \<rightarrow>\<^sup>S z = (x \<rightarrow>\<^sup>S (y \<rightarrow>\<^sup>S z))"}.\<close>

lemma sum_residuation_one:
  assumes "a \<in> S" "b \<in> S" "c \<in> S" "a = 1\<^sup>S \<or> b = 1\<^sup>S \<or> c = 1\<^sup>S"
  shows "(a *\<^sup>S b) \<rightarrow>\<^sup>S c = a \<rightarrow>\<^sup>S (b \<rightarrow>\<^sup>S c)"
  using sum_imp_D sum_imp_E sum_imp_closed sum_mult_closed sum_mult_neutr
        assms
  by metis

lemma sum_residuation_not_one:
  assumes "a \<in> S-{1\<^sup>S}" "b \<in> S-{1\<^sup>S}" "c \<in> S-{1\<^sup>S}"
  shows "(a *\<^sup>S b) \<rightarrow>\<^sup>S c = a \<rightarrow>\<^sup>S (b \<rightarrow>\<^sup>S c)"
proof -
  from assms
   consider (1) "floor a = floor b" "floor b = floor c"
    | (2) "floor a = floor b" "floor b <\<^sup>I floor c"
    | (3) "floor a = floor b" "floor c <\<^sup>I floor b"
    | (4) "floor a <\<^sup>I floor b" "floor b = floor c"
    | (5) "floor a <\<^sup>I floor b" "floor b <\<^sup>I floor c"
    | (6) "floor a <\<^sup>I floor b" "floor c <\<^sup>I floor b"
    | (7) "floor b <\<^sup>I floor a" "floor b = floor c"
    | (8) "floor b <\<^sup>I floor a" "floor b <\<^sup>I floor c"
    | (9) "floor b <\<^sup>I floor a" "floor c <\<^sup>I floor b"
     using trichotomy floor_prop by meson
  then
  show ?thesis
  proof(cases)
    case 1
    then
    have "(a *\<^sup>S b) \<rightarrow>\<^sup>S c = (a *\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a b) \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a c"
      using sum_imp_B sum_mult_A assms floor_mult_closed floor_prop by metis
    also
    have "\<dots> = a \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a (b \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>a c)"
      using "1" assms family_of_hoops floor_prop hoop.residuation by metis
    also
    have "\<dots> = a \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>b (b \<rightarrow>\<^sup>f\<^sup>l\<^sup>o\<^sup>o\<^sup>r \<^sup>b c)"
      using "1" by simp
    also
    have "\<dots> = a \<rightarrow>\<^sup>S (b \<rightarrow>\<^sup>S c)"
      using "1" sum_imp_A assms floor_imp_closed floor_prop by metis
    finally
    show ?thesis
      by auto
  next
    case 2
    then
    show ?thesis
      using sum_imp.simps(2,5) sum_mult_not_one assms floor_prop by metis
  next
    case 3
    then
    show ?thesis
      using sum_imp.simps(3) sum_mult_not_one assms floor_prop by metis
  next
    case 4
    then
    have "(a *\<^sup>S b) \<rightarrow>\<^sup>S c = 1\<^sup>S"
      using "4" sum_imp.simps(2) sum_mult.simps(2) assms by metis
    moreover
    have "b \<rightarrow>\<^sup>S c = 1\<^sup>S \<or> (b \<rightarrow>\<^sup>S c \<in> S-{1\<^sup>S} \<and> floor (b \<rightarrow>\<^sup>S c) = floor b)"
      using "4"(2) sum_imp_closed_not_one sum_imp_floor assms(2,3) by blast
    ultimately 
    show ?thesis
      using "4"(1) sum_imp.simps(2,5) assms(1) by metis
  next
    case 5
    then
    show ?thesis  
      using sum_imp.simps(2,5) sum_mult.simps(2) assms floor_prop strict_trans
      by metis
  next
    case 6
    then
    show ?thesis
      using assms by auto
  next
    case 7
    then
    have "(a *\<^sup>S b) \<rightarrow>\<^sup>S c = (b \<rightarrow>\<^sup>S c)"
      using assms(1,2) by auto
    moreover
    have "b \<rightarrow>\<^sup>S c = 1\<^sup>S \<or> (b \<rightarrow>\<^sup>S c \<in> S-{1\<^sup>S} \<and> floor (b \<rightarrow>\<^sup>S c) = floor b)"
      using "7"(2) sum_imp_closed_not_one sum_imp_floor assms(2,3) by blast
    ultimately
    show ?thesis
      using "7"(1) sum_imp.simps(3,5) assms(1) by metis
  next
    case 8
    then
    show ?thesis
      using assms by auto
  next
    case 9
    then
    show ?thesis
      using sum_imp.simps(3) sum_mult.simps(3) assms floor_prop strict_trans 
      by metis
  qed
qed

lemma sum_residuation:
  assumes "a \<in> S" "b \<in> S" "c \<in> S"
  shows "(a *\<^sup>S b) \<rightarrow>\<^sup>S c = a \<rightarrow>\<^sup>S (b \<rightarrow>\<^sup>S c)"
  using assms sum_residuation_one sum_residuation_not_one by blast

subsubsection\<open>Main result\<close>

sublocale hoop "S" "(*\<^sup>S)" "(\<rightarrow>\<^sup>S)" "1\<^sup>S"
proof
  show "x *\<^sup>S y \<in> S" if "x \<in> S" "y \<in> S" for x y
    using that sum_mult_closed by simp
next
  show "x \<rightarrow>\<^sup>S y \<in> S" if "x \<in> S" "y \<in> S" for x y
    using that sum_imp_closed by simp
next
  show "1\<^sup>S \<in> S"
    by simp
next
  show "x *\<^sup>S y = y *\<^sup>S x" if "x \<in> S" "y \<in> S" for x y
    using that sum_mult_comm by simp
next
  show "x *\<^sup>S (y *\<^sup>S z) = (x *\<^sup>S y) *\<^sup>S z" if "x \<in> S" "y \<in> S" "z \<in> S" for x y z 
    using that sum_mult_assoc by simp
next
  show "x *\<^sup>S 1\<^sup>S = x" if "x \<in> S" for x
    using that sum_mult_neutr by simp
next
  show "x \<rightarrow>\<^sup>S x = 1\<^sup>S" if "x \<in> S" for x
    using that sum_imp_reflex by simp
next
  show "x *\<^sup>S (x \<rightarrow>\<^sup>S y) = y *\<^sup>S (y \<rightarrow>\<^sup>S x)" if "x \<in> S" "y \<in> S" for x y
    using that sum_divisibility by simp
next
  show "x \<rightarrow>\<^sup>S (y \<rightarrow>\<^sup>S z) = (x *\<^sup>S y) \<rightarrow>\<^sup>S z" if "x \<in> S" "y \<in> S" "z \<in> S" for x y z
    using that sum_residuation by simp
qed

end
                                         
end