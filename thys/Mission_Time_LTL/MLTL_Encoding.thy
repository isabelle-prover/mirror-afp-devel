section \<open> MLTL Encoding \<close>
theory MLTL_Encoding

imports Main

begin

subsection \<open> Syntax \<close>

datatype (atoms_mltl: 'a) mltl =
    True_mltl                                     ("True\<^sub>m")
  | False_mltl                                    ("False\<^sub>m")
  | Prop_mltl 'a                                  ("Prop\<^sub>m '(_')")
  | Not_mltl "'a mltl"                            ("Not\<^sub>m _" [85] 85)
  | And_mltl "'a mltl" "'a mltl"                  ("_ And\<^sub>m _" [82, 82] 81)
  | Or_mltl "'a mltl" "'a mltl"                   ("_ Or\<^sub>m _" [81, 81] 80)
  | Future_mltl "nat" "nat" "'a mltl"             ("F\<^sub>m '[_',_'] _" [88, 88, 88] 87)
  | Global_mltl "nat" "nat" "'a mltl"             ("G\<^sub>m '[_',_'] _" [88, 88, 88] 87)
  | Until_mltl "'a mltl" "nat" "nat" "'a mltl"    ("_ U\<^sub>m '[_',_'] _" [84, 84, 84, 84] 83)
  | Release_mltl "'a mltl" "nat" "nat" "'a mltl"  ("_ R\<^sub>m '[_',_'] _" [84, 84, 84, 84] 83)

definition Implies_mltl ("_ Implies\<^sub>m _" [81, 81] 80)
  where "\<phi> Implies\<^sub>m \<psi> \<equiv> Not\<^sub>m \<phi> Or\<^sub>m \<psi>"

definition Iff_mltl ("_ Iff\<^sub>m _" [81, 81] 80)
  where "\<phi> Iff\<^sub>m \<psi> \<equiv> (\<phi> Implies\<^sub>m \<psi>) And\<^sub>m (\<psi> Implies\<^sub>m \<phi>)"

subsubsection \<open> Binding Examples \<close>
(*Not binds more tightly than And, Or*)
value "Not\<^sub>m Prop\<^sub>m (p) And\<^sub>m Prop\<^sub>m (q) =
       And_mltl (Not_mltl (Prop_mltl p)) (Prop_mltl q)"
(*And binds more tightly than Or*)
value "p And\<^sub>m q Or\<^sub>m r = Or_mltl (And_mltl p q) r"
(*Future and Global binds tighest*)
value "F\<^sub>m [0, 1] p And\<^sub>m q = And_mltl (Future_mltl 0 1 p) q"
(*Until and Release bind tighter than And/Or*)
value "p U\<^sub>m [0,1] q And\<^sub>m r = And_mltl (Until_mltl p 0 1 q) r"

subsection \<open> Semantics \<close>

(* NOTE: Added \<pi> \<noteq> [] in Prop_mltl *)
primrec semantics_mltl :: "['a set list, 'a mltl] \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>m _" [80,80] 80)
where
  "\<pi> \<Turnstile>\<^sub>m True\<^sub>m = True"
| "\<pi> \<Turnstile>\<^sub>m False\<^sub>m = False"
| "\<pi> \<Turnstile>\<^sub>m Prop\<^sub>m (q) = (\<pi> \<noteq> [] \<and> q \<in> (\<pi> ! 0))"
| "\<pi> \<Turnstile>\<^sub>m Not\<^sub>m \<phi> = (\<not> \<pi> \<Turnstile>\<^sub>m \<phi>)"
| "\<pi> \<Turnstile>\<^sub>m \<phi> And\<^sub>m \<psi> = (\<pi> \<Turnstile>\<^sub>m \<phi> \<and> \<pi> \<Turnstile>\<^sub>m \<psi>)"
| "\<pi> \<Turnstile>\<^sub>m \<phi> Or\<^sub>m \<psi> = (\<pi> \<Turnstile>\<^sub>m \<phi> \<or> \<pi> \<Turnstile>\<^sub>m \<psi>)"
| "\<pi> \<Turnstile>\<^sub>m (F\<^sub>m [a, b] \<phi>) = (a \<le> b \<and> length \<pi> > a \<and>
      (\<exists>i::nat. (i \<ge> a \<and> i \<le> b) \<and> (drop i \<pi>) \<Turnstile>\<^sub>m \<phi>))"
| "\<pi> \<Turnstile>\<^sub>m (G\<^sub>m [a, b] \<phi>) = (a \<le> b \<and> (length \<pi> \<le> a \<or>
      (\<forall>i::nat. (i \<ge> a \<and> i \<le> b) \<longrightarrow> (drop i \<pi>) \<Turnstile>\<^sub>m \<phi>)))"
| "\<pi> \<Turnstile>\<^sub>m (\<phi> U\<^sub>m [a, b] \<psi>) =  (a \<le> b \<and> length \<pi> > a \<and>
      (\<exists>i::nat. (i \<ge> a \<and> i \<le> b) \<and> ((drop i \<pi>) \<Turnstile>\<^sub>m \<psi>
        \<and> (\<forall>j. j \<ge> a \<and> j<i \<longrightarrow> (drop j \<pi>) \<Turnstile>\<^sub>m \<phi>))))"
| "\<pi> \<Turnstile>\<^sub>m (\<phi> R\<^sub>m [a, b] \<psi>) = (a \<le> b \<and> (length \<pi> \<le> a \<or>
      (\<forall>i::nat. (i \<ge> a \<and> i \<le> b) \<longrightarrow> (((drop i \<pi>) \<Turnstile>\<^sub>m \<psi>))) \<or>
      (\<exists>j. j \<ge> a \<and> j \<le> b-1 \<and> (drop j \<pi>) \<Turnstile>\<^sub>m \<phi> \<and>
         (\<forall>k. a \<le> k \<and> k \<le> j \<longrightarrow> (drop k \<pi>) \<Turnstile>\<^sub>m \<psi>))))"

subsubsection \<open> Examples \<close>

lemma
  "[{0::nat}] \<Turnstile>\<^sub>m Not\<^sub>m (F\<^sub>m [0,2] Prop\<^sub>m (0)) = False"
  by auto

lemma
  "[{0::nat}] \<Turnstile>\<^sub>m F\<^sub>m [0,2] (Not\<^sub>m Prop\<^sub>m (0)) = True"
  proof-
    have "\<not> (drop 1 [{0}] \<noteq> [] \<and> 0 \<in> drop 1 [{0}] ! 0)"
      by simp
    then have "(\<exists>i. (0 \<le> i \<and> i \<le> 2) \<and> \<not> (drop i [{0}] \<noteq> [] \<and> 0 \<in> drop i [{0}] ! 0))"
      by auto
    then show ?thesis
      unfolding semantics_mltl.simps
      by blast
  qed

lemma
  "[{0::nat}] \<Turnstile>\<^sub>m G\<^sub>m [0,2] Prop\<^sub>m (0::nat) = False"
  by auto


end