(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Finite Fields\<close>

text \<open>We provide an implementation for $GF(p)$ -- the field with $p$ elements for some
  prime $p$ -- by integers. Correctness of the implementation is proven by
  transfer rules to the type-based version of $GF(p)$.\<close>

theory Finite_Field_Record_Based
imports
  Finite_Field
  Arithmetic_Record_Based
begin

context
  fixes p :: int
begin
definition plus_p :: "int \<Rightarrow> int \<Rightarrow> int" where
  "plus_p x y \<equiv> let z = x + y in if z \<ge> p then z - p else z"

definition minus_p :: "int \<Rightarrow> int \<Rightarrow> int" where
  "minus_p x y \<equiv> let z = x - y in if z < 0 then z + p else z"

definition uminus_p :: "int \<Rightarrow> int" where
  "uminus_p x = (if x = 0 then 0 else p - x)"

definition mult_p :: "int \<Rightarrow> int \<Rightarrow> int" where
  "mult_p x y = (x * y mod p)"

fun power_p :: "int \<Rightarrow> nat \<Rightarrow> int" where
  "power_p x n = (if n = 0 then 1 else
    let (d,r) = Divides.divmod_nat n 2;
       rec = power_p (mult_p x x) d in
    if r = 0 then rec else mult_p rec x)"

text \<open>In experiments with Berlekamp-factorization (where the prime $p$ is usually small),
  it turned out that taking the below implementation of inverse via exponentiation
  is faster than the one based on the extended Euclidean algorithm.\<close>

definition inverse_p :: "int \<Rightarrow> int" where
  "inverse_p x = (if x = 0 then 0 else power_p x (nat (p - 2)))"

definition divide_p :: "int \<Rightarrow> int \<Rightarrow> int"  where
  "divide_p x y = mult_p x (inverse_p y)"

definition finite_field_ops :: "int arith_ops_record" where
  "finite_field_ops \<equiv> Arith_Ops_Record
      0
      1
      plus_p
      mult_p
      minus_p
      uminus_p
      divide_p
      inverse_p
      (\<lambda> x y . if y = 0 then x else 0)
      (\<lambda> x . if x = 0 then 0 else 1)
      (\<lambda> x . x)
      (\<lambda> x. 0 \<le> x \<and> x < p)"

end

(* ******************************************************************************** *)
subsubsection \<open>Transfer Relation\<close>
locale mod_ring_locale =
  fixes p :: int and ty :: "'a :: nontriv itself"
  assumes p: "p = int CARD('a)"
begin
lemma nat_p: "nat p = CARD('a)" unfolding p by simp

definition mod_ring_rel :: "int \<Rightarrow> 'a mod_ring \<Rightarrow> bool" where
  "mod_ring_rel x x' = (x = to_int_mod_ring x')"

lemma to_int_mod_ring_inj: "to_int_mod_ring x = to_int_mod_ring y \<Longrightarrow> x = y"
  using injD[OF inj_to_int_mod_ring] .

(* domain transfer rules *)
lemma Domainp_mod_ring_rel [transfer_domain_rule]:
  "Domainp (mod_ring_rel) = (\<lambda> v. v \<in> {0 ..< p})"
proof -
  {
    fix v :: int
    assume *: "0 \<le> v" "v < p"
    have "Domainp mod_ring_rel v"
    proof
      show "mod_ring_rel v (of_int_mod_ring v)" unfolding mod_ring_rel_def using * p by auto
    qed
  } note * = this
  show ?thesis
    by (intro ext iffI, insert range_to_int_mod_ring[where 'a = 'a] *, auto simp: mod_ring_rel_def p)
qed

(* left/right/bi-unique *)
lemma bi_unique_mod_ring_rel [transfer_rule]:
  "bi_unique mod_ring_rel" "left_unique mod_ring_rel" "right_unique mod_ring_rel"
  unfolding mod_ring_rel_def bi_unique_def left_unique_def right_unique_def
  using to_int_mod_ring_inj by auto

(* left/right-total *)
lemma right_total_mod_ring_rel [transfer_rule]: "right_total mod_ring_rel"
  unfolding mod_ring_rel_def right_total_def by simp


(* ************************************************************************************ *)
subsubsection \<open>Transfer Rules\<close>

(* 0 / 1 *)
lemma mod_ring_0[transfer_rule]: "mod_ring_rel 0 0" unfolding mod_ring_rel_def by simp
lemma mod_ring_1[transfer_rule]: "mod_ring_rel 1 1" unfolding mod_ring_rel_def by simp

(* addition *)
lemma plus_p_mod_def: assumes x: "x \<in> {0 ..< p}" and y: "y \<in> {0 ..< p}"
  shows "plus_p p x y = ((x + y) mod p)"
proof (cases "p \<le> x + y")
  case False
  thus ?thesis using x y unfolding plus_p_def Let_def by auto
next
  case True
  from True x y have *: "p > 0" "0 \<le> x + y - p" "x + y - p < p" by auto
  from True have id: "plus_p p x y = x + y - p" unfolding plus_p_def by auto
  show ?thesis unfolding id using * using mod_pos_pos_trivial by fastforce
qed

lemma mod_ring_plus[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel ===> mod_ring_rel) (plus_p p) (op +)"
proof -
  {
    fix x y :: "'a mod_ring"
    have "plus_p p (to_int_mod_ring x) (to_int_mod_ring y) = to_int_mod_ring (x + y)"
      by (transfer, subst plus_p_mod_def, auto, auto simp: p)
  } note * = this
  show ?thesis
    by (intro rel_funI, auto simp: mod_ring_rel_def *)
qed

(* subtraction *)
lemma minus_p_mod_def: assumes x: "x \<in> {0 ..< p}" and y: "y \<in> {0 ..< p}"
  shows "minus_p p x y = ((x - y) mod p)"
proof (cases "x - y < 0")
  case False
  thus ?thesis using x y unfolding minus_p_def Let_def by auto
next
  case True
  from True x y have *: "p > 0" "0 \<le> x - y + p" "x - y + p < p" by auto
  from True have id: "minus_p p x y = x - y + p" unfolding minus_p_def by auto
  show ?thesis unfolding id using * using mod_pos_pos_trivial by fastforce
qed

lemma mod_ring_minus[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel ===> mod_ring_rel) (minus_p p) (op -)"
proof -
  {
    fix x y :: "'a mod_ring"
    have "minus_p p (to_int_mod_ring x) (to_int_mod_ring y) = to_int_mod_ring (x - y)"
      by (transfer, subst minus_p_mod_def, auto simp: p)
  } note * = this
  show ?thesis
    by (intro rel_funI, auto simp: mod_ring_rel_def *)
qed

(* unary minus *)
lemma mod_ring_uminus[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel) (uminus_p p) uminus"
proof -
  {
    fix x :: "'a mod_ring"
    have "uminus_p p (to_int_mod_ring x) = to_int_mod_ring (uminus x)"
      by (transfer, auto simp: uminus_p_def p)
  } note * = this
  show ?thesis
    by (intro rel_funI, auto simp: mod_ring_rel_def *)
qed

(* multiplication *)
lemma mod_ring_mult[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel ===> mod_ring_rel) (mult_p p) (op *)"
proof -
  {
    fix x y :: "'a mod_ring"
    have "mult_p p (to_int_mod_ring x) (to_int_mod_ring y) = to_int_mod_ring (x * y)"
      by (transfer, auto simp: mult_p_def p)
  } note * = this
  show ?thesis
    by (intro rel_funI, auto simp: mod_ring_rel_def *)
qed

(* equality *)
lemma mod_ring_eq[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel ===> op =) (op =) (op =)"
  by (intro rel_funI, auto simp: mod_ring_rel_def to_int_mod_ring_inj)

(* power *)
lemma mod_ring_power[transfer_rule]: "(mod_ring_rel ===> op = ===> mod_ring_rel) (power_p p) (op ^)"
proof (intro rel_funI, clarify, unfold binary_power[symmetric], goal_cases)
  fix x y n
  assume xy: "mod_ring_rel x y"
  from xy show "mod_ring_rel (power_p p x n) (binary_power y n)"
  proof (induct y n arbitrary: x rule: binary_power.induct)
    case (1 x n y)
    note 1(2)[transfer_rule]
    show ?case
    proof (cases "n = 0")
      case True
      thus ?thesis by (simp add: mod_ring_1)
    next
      case False
      obtain d r where id: "Divides.divmod_nat n 2 = (d,r)" by force
      let ?int = "power_p p (mult_p p y y) d"
      let ?gfp = "binary_power (x * x) d"
      from False have id': "?thesis = (mod_ring_rel
         (if r = 0 then ?int else mult_p p ?int y)
         (if r = 0 then ?gfp else ?gfp * x))"
        unfolding power_p.simps[of _ _ n] binary_power.simps[of _ n] Let_def id split by simp
      have [transfer_rule]: "mod_ring_rel ?int ?gfp"
        by (rule 1(1)[OF False refl id[symmetric]], transfer_prover)
      show ?thesis unfolding id' by transfer_prover
    qed
  qed
qed

declare power_p.simps[simp del]

end

locale prime_field = mod_ring_locale p ty for p and ty :: "'a :: prime_card itself"
begin

lemma prime: "prime p" unfolding p using prime_card[where 'a = 'a] by simp

(* mod *)
lemma mod_ring_mod[transfer_rule]:
 "(mod_ring_rel ===> mod_ring_rel ===> mod_ring_rel) ((\<lambda> x y. if y = 0 then x else 0)) (op mod)"
proof -
  {
    fix x y :: "'a mod_ring"
    have "(if to_int_mod_ring y = 0 then to_int_mod_ring x else 0) = to_int_mod_ring (x mod y)"
      unfolding modulo_mod_ring_def by auto
  } note * = this
  show ?thesis
    by (intro rel_funI, auto simp: mod_ring_rel_def *[symmetric])
qed

(* normalize *)
lemma mod_ring_normalize[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel) ((\<lambda> x. if x = 0 then 0 else 1)) normalize"
proof -
  {
    fix x :: "'a mod_ring"
    have "(if to_int_mod_ring x = 0 then 0 else 1) = to_int_mod_ring (normalize x)"
      unfolding normalize_mod_ring_def by auto
  } note * = this
  show ?thesis
    by (intro rel_funI, auto simp: mod_ring_rel_def *[symmetric])
qed

(* unit_factor *)
lemma mod_ring_unit_factor[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel) (\<lambda> x. x) unit_factor"
proof -
  {
    fix x :: "'a mod_ring"
    have "to_int_mod_ring x = to_int_mod_ring (unit_factor x)"
      unfolding unit_factor_mod_ring_def by auto
  } note * = this
  show ?thesis
    by (intro rel_funI, auto simp: mod_ring_rel_def *[symmetric])
qed

(* inverse *)
lemma p2: "p \<ge> 2" using prime_ge_2_int[OF prime] by auto
lemma p2_ident: "int (CARD('a) - 2) = p - 2" using p2 unfolding p by simp

lemma mod_ring_inverse[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel) (inverse_p p) inverse"
proof (intro rel_funI)
  fix x y
  assume [transfer_rule]: "mod_ring_rel x y"
  show "mod_ring_rel (inverse_p p x) (inverse y)"
    unfolding inverse_p_def inverse_mod_ring_def
    apply (transfer_prover_start)
    apply (transfer_step)+
    apply (unfold p2_ident)
    apply (rule refl)
    done
qed

(* division *)
lemma mod_ring_divide[transfer_rule]: "(mod_ring_rel ===> mod_ring_rel ===> mod_ring_rel)
  (divide_p p) (op /)"
  unfolding divide_p_def[abs_def] divide_mod_ring_def[abs_def] inverse_mod_ring_def[symmetric]
  by transfer_prover

lemma mod_ring_rel_unsafe: assumes "x < CARD('a)"
  shows "mod_ring_rel (int x) (of_nat x)" "0 < x \<Longrightarrow> of_nat x \<noteq> (0 :: 'a mod_ring)"
proof -
  have id: "of_nat x = (of_int (int x) :: 'a mod_ring)" by simp
  show "mod_ring_rel (int x) (of_nat x)" "0 < x \<Longrightarrow> of_nat x \<noteq> (0 :: 'a mod_ring)" unfolding id
  unfolding mod_ring_rel_def
  proof (auto simp add: assms of_int_of_int_mod_ring)
    assume "0 < x" with assms
    have "of_int_mod_ring (int x) \<noteq> (0 :: 'a mod_ring)"
      by (metis (no_types) less_imp_of_nat_less less_irrefl of_nat_0_le_iff of_nat_0_less_iff to_int_mod_ring_0 to_int_mod_ring_of_int_mod_ring)
    thus "of_int_mod_ring (int x) = (0 :: 'a mod_ring) \<Longrightarrow> False" by blast
  qed
qed

lemma finite_field_ops: "field_ops (finite_field_ops p) mod_ring_rel"
  by (unfold_locales, auto simp:
  finite_field_ops_def
  bi_unique_mod_ring_rel
  right_total_mod_ring_rel
  mod_ring_divide
  mod_ring_plus
  mod_ring_minus
  mod_ring_uminus
  mod_ring_inverse
  mod_ring_mod
  mod_ring_unit_factor
  mod_ring_normalize
  mod_ring_mult
  mod_ring_eq
  mod_ring_0
  mod_ring_1
  Domainp_mod_ring_rel)

(* ********************************************************** *)

lemma assumes rel: "mod_ring_rel x1 x2" "mod_ring_rel y1 y2"
  and x1: "x1 \<noteq> 0"
  shows "mult_p p (inverse_p p x1) y1 = divide_p p y1 x1"
proof -
  note [transfer_rule] = rel
  from x1 have "x2 \<noteq> 0" by transfer
  hence "inverse x2 * y2 = y2 / x2" by (simp add: field_simps)
  from this[untransferred] show ?thesis unfolding p .
qed
end

text \<open>Once we have proven the soundness of the implementation, we do not care any longer
  that @{typ "'a mod_ring"} has been defined internally via lifting. Disabling the transfer-rules
  will hide the internal definition in further applications of transfer.\<close>
lifting_forget mod_ring.lifting

end
