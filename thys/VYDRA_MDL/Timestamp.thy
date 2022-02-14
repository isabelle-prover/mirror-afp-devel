theory Timestamp
  imports "HOL-Library.Extended_Nat" "HOL-Library.Extended_Real"
begin

class timestamp = comm_monoid_add + semilattice_sup +
  fixes tfin :: "'a set" and \<iota> :: "nat \<Rightarrow> 'a"
  assumes \<iota>_mono: "\<And>i j. i \<le> j \<Longrightarrow> \<iota> i \<le> \<iota> j"
    and \<iota>_fin: "\<And>i. \<iota> i \<in> tfin"
    and \<iota>_progressing: "x \<in> tfin \<Longrightarrow> \<exists>j. \<not>\<iota> j \<le> \<iota> i + x"
    and zero_tfin: "0 \<in> tfin"
    and tfin_closed: "c \<in> tfin \<Longrightarrow> d \<in> tfin \<Longrightarrow> c + d \<in> tfin"
    and add_mono: "c \<le> d \<Longrightarrow> a + c \<le> a + d"
    and add_pos: "a \<in> tfin \<Longrightarrow> 0 < c \<Longrightarrow> a < a + c"
begin

lemma add_mono_comm:
  fixes a :: 'a
  shows "c \<le> d \<Longrightarrow> c + a \<le> d + a"
  by (auto simp: add.commute add_mono)

end

instantiation prod :: (comm_monoid_add, comm_monoid_add) comm_monoid_add
begin

definition zero_prod :: "'a \<times> 'b" where
  "zero_prod = (zero_class.zero, zero_class.zero)"

fun plus_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
  "(a, b) + (c, d) = (a + c, b + d)"

instance
  by standard (auto simp: zero_prod_def ac_simps)

end

instantiation enat :: timestamp
begin

definition tfin_enat :: "enat set" where
  "tfin_enat = UNIV - {\<infinity>}"

definition \<iota>_enat :: "nat \<Rightarrow> enat" where
  "\<iota>_enat n = n"

instance
  by standard (auto simp add: \<iota>_enat_def tfin_enat_def dest!: leD)

end

instantiation ereal :: timestamp
begin

definition \<iota>_ereal :: "nat \<Rightarrow> ereal" where
  "\<iota>_ereal n = ereal n"

definition tfin_ereal :: "ereal set" where
  "tfin_ereal = UNIV - {-\<infinity>, \<infinity>}"

lemma ereal_add_pos:
  fixes a :: ereal
  shows "a \<in> tfin \<Longrightarrow> 0 < c \<Longrightarrow> a < a + c"
  by (auto simp: tfin_ereal_def) (metis add.right_neutral ereal_add_cancel_left ereal_le_add_self order_less_le)

instance
  by standard (auto simp add: \<iota>_ereal_def tfin_ereal_def add.commute
      ereal_add_le_add_iff2 not_le less_PInf_Ex_of_nat ereal_less_ereal_Ex reals_Archimedean2 intro: ereal_add_pos)

end

class timestamp_strict = timestamp +
  assumes timestamp_strict_total: "a \<le> b \<or> b \<le> a"
    and add_mono_strict: "c < d \<Longrightarrow> a + c < a + d"

instantiation nat :: timestamp_strict
begin

definition tfin_nat :: "nat set" where
  "tfin_nat = UNIV"

definition \<iota>_nat :: "nat \<Rightarrow> nat" where
  "\<iota>_nat n = n"

instance
  by standard (auto simp add: \<iota>_nat_def tfin_nat_def dest!: leD)

end

instantiation real :: timestamp_strict
begin

definition tfin_real :: "real set" where "tfin_real = UNIV"

definition \<iota>_real :: "nat \<Rightarrow> real" where "\<iota>_real n = real n"
instance
  by standard (auto simp: tfin_real_def \<iota>_real_def not_le reals_Archimedean2)

end

class timestamp_total = timestamp +
  assumes timestamp_total: "a \<le> b \<or> b \<le> a"
  assumes aux: "0 \<le> a \<Longrightarrow> a \<le> c \<Longrightarrow> a \<in> tfin \<Longrightarrow> c \<in> tfin \<Longrightarrow> 0 \<le> b \<Longrightarrow> b \<notin> tfin \<Longrightarrow> c < a + b"

instantiation enat :: timestamp_total
begin

instance
  apply standard
   apply (auto simp: tfin_enat_def)
  done

end

instantiation ereal :: timestamp_total
begin

instance
  apply standard
   apply (auto simp: tfin_ereal_def)
  done

end

class timestamp_total_strict = timestamp_total +
  assumes add_mono_strict_total: "c < d \<Longrightarrow> a + c < a + d"

instantiation nat :: timestamp_total_strict
begin

instance
  apply standard
  apply (auto simp: tfin_nat_def)
  done

end

instantiation real :: timestamp_total_strict
begin

instance
  apply standard
  apply (auto simp: tfin_real_def)
  done

end

end
