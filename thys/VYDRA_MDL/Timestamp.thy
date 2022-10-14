theory Timestamp
  imports "HOL-Library.Extended_Nat" "HOL-Library.Extended_Real"
begin

class embed_nat =
  fixes \<iota> :: "nat \<Rightarrow> 'a"

class tfin =
  fixes tfin :: "'a set"

class timestamp = comm_monoid_add + semilattice_sup + embed_nat + tfin +
  assumes \<iota>_mono: "\<And>i j. i \<le> j \<Longrightarrow> \<iota> i \<le> \<iota> j"
    and \<iota>_tfin: "\<And>i. \<iota> i \<in> tfin"
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

(* Extending time domain with infinity (None). *)

instantiation option :: (timestamp) timestamp
begin

definition tfin_option :: "'a option set" where
  "tfin_option = Some ` tfin"

definition \<iota>_option :: "nat \<Rightarrow> 'a option" where
  "\<iota>_option = Some \<circ> \<iota>"

definition zero_option :: "'a option" where
  "zero_option = Some 0"

definition plus_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "plus_option x y = (case x of None \<Rightarrow> None | Some x' \<Rightarrow> (case y of None \<Rightarrow> None | Some y' \<Rightarrow> Some (x' + y')))"

definition sup_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "sup_option x y = (case x of None \<Rightarrow> None | Some x' \<Rightarrow> (case y of None \<Rightarrow> None | Some y' \<Rightarrow> Some (sup x' y')))"

definition less_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
  "less_option x y = (case x of None \<Rightarrow> False | Some x' \<Rightarrow> (case y of None \<Rightarrow> True | Some y' \<Rightarrow> x' < y'))"

definition less_eq_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
  "less_eq_option x y = (case x of None \<Rightarrow> x = y | Some x' \<Rightarrow> (case y of None \<Rightarrow> True | Some y' \<Rightarrow> x' \<le> y'))"

instance
  apply standard
                  apply (auto simp: plus_option_def add.assoc split: option.splits)[1]
                 apply (auto simp: plus_option_def add.commute split: option.splits)[1]
                apply (auto simp: zero_option_def plus_option_def split: option.splits)[1]
               apply (auto simp: less_option_def less_eq_option_def split: option.splits)[1]
              apply (auto simp: less_eq_option_def split: option.splits)[3]
           apply (auto simp: sup_option_def less_eq_option_def split: option.splits)[3]
        apply (auto simp: \<iota>_option_def less_eq_option_def intro: \<iota>_mono)[1]
       apply (auto simp: tfin_option_def \<iota>_option_def intro: \<iota>_tfin)[1]
      apply (auto simp: tfin_option_def \<iota>_option_def plus_option_def less_eq_option_def intro: \<iota>_progressing)[1]
     apply (auto simp: tfin_option_def zero_option_def intro: zero_tfin)[1]
    apply (auto simp: tfin_option_def plus_option_def intro: tfin_closed)[1]
   apply (auto simp: plus_option_def less_eq_option_def intro: add_mono split: option.splits)[1]
  apply (auto simp: tfin_option_def zero_option_def plus_option_def less_option_def intro: add_pos split: option.splits)
  done

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
  by standard (auto simp add: \<iota>_ereal_def tfin_ereal_def add.commute ereal_add_le_add_iff2 not_le
      less_PInf_Ex_of_nat ereal_less_ereal_Ex reals_Archimedean2 intro: ereal_add_pos)

end

class timestamp_total = timestamp +
  assumes timestamp_total: "a \<le> b \<or> b \<le> a"
  assumes timestamp_tfin_le_not_tfin: "0 \<le> a \<Longrightarrow> a \<in> tfin \<Longrightarrow> 0 \<le> b \<Longrightarrow> b \<notin> tfin \<Longrightarrow> a \<le> b"
begin

lemma add_not_tfin: "0 \<le> a \<Longrightarrow> a \<in> tfin \<Longrightarrow> a \<le> c \<Longrightarrow> c \<in> tfin \<Longrightarrow> 0 \<le> b \<Longrightarrow> b \<notin> tfin \<Longrightarrow> c < a + b"
  by (metis add_0_left local.add_mono_comm timestamp_tfin_le_not_tfin dual_order.order_iff_strict dual_order.strict_trans1)

end

instantiation enat :: timestamp_total
begin

instance
  by standard (auto simp: tfin_enat_def)

end

instantiation ereal :: timestamp_total
begin

instance
  by standard (auto simp: tfin_ereal_def)

end

class timestamp_strict = timestamp +
  assumes add_mono_strict: "c < d \<Longrightarrow> a + c < a + d"

class timestamp_total_strict = timestamp_total + timestamp_strict

instantiation nat :: timestamp_total_strict
begin

definition tfin_nat :: "nat set" where
  "tfin_nat = UNIV"

definition \<iota>_nat :: "nat \<Rightarrow> nat" where
  "\<iota>_nat n = n"

instance
  by standard (auto simp: tfin_nat_def \<iota>_nat_def dest!: leD)

end

instantiation real :: timestamp_total_strict
begin

definition tfin_real :: "real set" where "tfin_real = UNIV"

definition \<iota>_real :: "nat \<Rightarrow> real" where "\<iota>_real n = real n"

instance
  by standard (auto simp: tfin_real_def \<iota>_real_def not_le reals_Archimedean2)

end

instantiation prod :: (comm_monoid_add, comm_monoid_add) comm_monoid_add
begin

definition zero_prod :: "'a \<times> 'b" where
  "zero_prod = (0, 0)"

fun plus_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
  "(a, b) + (c, d) = (a + c, b + d)"

instance
  by standard (auto simp: zero_prod_def ac_simps)

end

end
