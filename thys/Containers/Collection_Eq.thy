(*  Title:      Containers/Collection_Eq.thy
    Author:     Andreas Lochbihler, KIT *)

theory Collection_Eq imports
  Auxiliary
begin

section {* A type class for optional equality testing *}

class ceq =
  fixes ceq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) option"
  assumes ceq: "ceq = Some eq \<Longrightarrow> eq = op ="
begin

lemma ID_ceq: "ID ceq = Some eq \<Longrightarrow> eq = op ="
unfolding ID_def id_apply by(rule ceq)

abbreviation ceq' :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where "ceq' \<equiv> the (ID ceq)"

end

syntax "_CEQ" :: "type => logic"  ("(1CEQ/(1'(_')))")

parse_translation {*
let
  fun ceq_tr [ty] =
     (Syntax.const @{syntax_const "_constrain"} $ Syntax.const @{const_syntax "ceq"} $
       (Syntax.const @{type_syntax option} $ 
         (Syntax.const @{type_syntax fun} $ ty $ 
           (Syntax.const @{type_syntax fun} $ ty $ Syntax.const @{type_syntax bool}))))
    | ceq_tr ts = raise TERM ("ceq_tr", ts);
in [(@{syntax_const "_CEQ"}, K ceq_tr)] end
*}

typed_print_translation {*
let
  fun ceq_tr' ctxt
    (Type (@{type_name option}, [Type (@{type_name fun}, [T, _])])) ts =
    Term.list_comb (Syntax.const @{syntax_const "_CEQ"} $ Syntax_Phases.term_of_typ ctxt T, ts)
  | ceq_tr' _ _ _ = raise Match;
in [(@{const_syntax ceq}, ceq_tr')]
end
*}

definition is_ceq :: "'a :: ceq itself \<Rightarrow> bool"
where "is_ceq _ \<longleftrightarrow> ID CEQ('a) \<noteq> None"

subsection {* Type class instances for HOL types *}

instantiation unit :: ceq begin
definition "CEQ(unit) = Some (\<lambda>_ _. True)"
instance by(intro_classes)(simp add: ceq_unit_def fun_eq_iff)
end

lemma is_ceq_unit [simp, code_post]: "is_ceq TYPE(unit)"
by(simp add: is_ceq_def ceq_unit_def ID_Some)

instantiation bool :: ceq begin
definition "CEQ(bool) = Some op ="
instance by(intro_classes)(simp add: ceq_bool_def)
end

lemma is_ceq_bool [simp, code_post]: "is_ceq TYPE(bool)"
by(simp add: is_ceq_def ceq_bool_def ID_Some)

instantiation nat :: ceq begin
definition "CEQ(nat) = Some op ="
instance by(intro_classes)(simp add: ceq_nat_def)
end

lemma is_ceq_nat [simp, code_post]: "is_ceq TYPE(nat)"
by(simp add: is_ceq_def ceq_nat_def ID_Some)

instantiation int :: ceq begin
definition "CEQ(int) = Some op ="
instance by(intro_classes)(simp add: ceq_int_def)
end

lemma is_ceq_int [simp, code_post]: "is_ceq TYPE(int)"
by(simp add: is_ceq_def ceq_int_def ID_Some)

instantiation Enum.finite_1 :: ceq begin
definition "CEQ(Enum.finite_1) = Some op ="
instance by(intro_classes)(simp add: ceq_finite_1_def)
end

lemma is_ceq_finite_1 [simp, code_post]: "is_ceq TYPE(Enum.finite_1)"
by(simp add: is_ceq_def ceq_finite_1_def ID_Some)

instantiation Enum.finite_2 :: ceq begin
definition "CEQ(Enum.finite_2) = Some op ="
instance by(intro_classes)(simp add: ceq_finite_2_def)
end

lemma is_ceq_finite_2 [simp, code_post]: "is_ceq TYPE(Enum.finite_2)"
by(simp add: is_ceq_def ceq_finite_2_def ID_Some)

instantiation Enum.finite_3 :: ceq begin
definition "CEQ(Enum.finite_3) = Some op ="
instance by(intro_classes)(simp add: ceq_finite_3_def)
end

lemma is_ceq_finite_3 [simp, code_post]: "is_ceq TYPE(Enum.finite_3)"
by(simp add: is_ceq_def ceq_finite_3_def ID_Some)

instantiation Enum.finite_4 :: ceq begin
definition "CEQ(Enum.finite_4) = Some op ="
instance by(intro_classes)(simp add: ceq_finite_4_def)
end

lemma is_ceq_finite_4 [simp, code_post]: "is_ceq TYPE(Enum.finite_4)"
by(simp add: is_ceq_def ceq_finite_4_def ID_Some)

instantiation Enum.finite_5 :: ceq begin
definition "CEQ(Enum.finite_5) = None"
instance by(intro_classes)(simp add: ceq_finite_5_def)
end

lemma is_ceq_finite_5 [simp]: "\<not> is_ceq TYPE(Enum.finite_5)"
by(simp add: is_ceq_def ceq_finite_5_def ID_None)

instantiation integer :: ceq begin
definition "CEQ(integer) = Some op ="
instance by(intro_classes)(simp add: ceq_integer_def)
end

lemma is_ceq_integer [simp, code_post]: "is_ceq TYPE(integer)"
by(simp add: is_ceq_def ceq_integer_def ID_Some)

instantiation natural :: ceq begin
definition "CEQ(natural) = Some op ="
instance by(intro_classes)(simp add: ceq_natural_def)
end

lemma is_ceq_natural [simp, code_post]: "is_ceq TYPE(natural)"
by(simp add: is_ceq_def ceq_natural_def ID_Some)

instantiation nibble :: ceq begin
definition "CEQ(nibble) \<equiv> Some op ="
instance by intro_classes(simp add: ceq_nibble_def)
end

lemma is_ceq_nibble [simp, code_post]: "is_ceq TYPE(nibble)"
by(simp add: is_ceq_def ceq_nibble_def ID_Some)

instantiation char :: ceq begin
definition "CEQ(char) = Some op ="
instance by(intro_classes)(simp add: ceq_char_def)
end

lemma is_ceq_char [simp, code_post]: "is_ceq TYPE(char)"
by(simp add: is_ceq_def ceq_char_def ID_Some)

instantiation String.literal :: ceq begin
definition "CEQ(String.literal) = Some op ="
instance by(intro_classes)(simp add: ceq_literal_def)
end

lemma is_ceq_literal [simp, code_post]: "is_ceq TYPE(String.literal)"
by(simp add: is_ceq_def ceq_literal_def ID_Some)

instantiation sum :: (ceq, ceq) ceq begin
text {* Do not use @{term "op ="} because that would pull in @{class equal} on component types for code generation *}
definition "CEQ('a + 'b) = 
  (case ID CEQ('a) of None \<Rightarrow> None
   | Some eq_a \<Rightarrow>
     case ID CEQ('b) of None \<Rightarrow> None
     | Some eq_b \<Rightarrow> 
       Some (\<lambda>x y. case x of Inl xl \<Rightarrow> (case y of Inl yl \<Rightarrow> eq_a xl yl | _ \<Rightarrow> False)
                   | Inr xr \<Rightarrow> (case y of Inr yr \<Rightarrow> eq_b xr yr | _ \<Rightarrow> False)))"
instance
proof(intro_classes)
  fix eq
  assume "CEQ('a + 'b) = Some eq"
  then obtain eq_a eq_b where a: "ID CEQ('a) = Some eq_a" 
    and b: "ID CEQ('b) = Some eq_b"
    and eq: "\<And>x y. eq x y = (case x of Inl xl \<Rightarrow> (case y of Inl yl \<Rightarrow> eq_a xl yl | _ \<Rightarrow> False) 
                             | Inr xr \<Rightarrow> (case y of Inr yr \<Rightarrow> eq_b xr yr | _ \<Rightarrow> False))"
    by(auto simp add: ceq_sum_def split: option.splits)
  from ID_ceq[OF a] ID_ceq[OF b] show "eq = op ="
    by(simp add: fun_eq_iff eq split: sum.split)
qed
end

lemma is_ceq_sum [simp, code_post]:
  "is_ceq TYPE('a + 'b) \<longleftrightarrow> is_ceq TYPE('a :: ceq) \<and> is_ceq TYPE('b :: ceq)"
by(simp add: is_ceq_def ceq_sum_def ID_Some ID_None split: option.split)

instantiation prod :: (ceq, ceq) ceq begin
definition "CEQ('a * 'b) =
  (case ID CEQ('a) of None \<Rightarrow> None
   | Some eq_a \<Rightarrow>
     case ID CEQ('b) of None \<Rightarrow> None
     | Some eq_b \<Rightarrow>
       Some (\<lambda>(x1, x2) (y1, y2). eq_a x1 y1 \<and> eq_b x2 y2))"
instance
proof
  fix eq
  assume "CEQ('a * 'b) = Some eq"
  then obtain eq_a eq_b
    where a: "ID CEQ('a) = Some eq_a" 
    and b: "ID CEQ('b) = Some eq_b"
    and eq: "\<And>x1 x2 y1 y2. eq (x1, x2) (y1, y2) \<longleftrightarrow> eq_a x1 y1 \<and> eq_b x2 y2"
    by(auto simp add: ceq_prod_def split: option.split_asm)
  from ID_ceq[OF a] ID_ceq[OF b] show "eq = op =" by(simp add: fun_eq_iff eq)
qed
end

lemma is_ceq_prod [simp, code_post]:
  "is_ceq TYPE('a \<times> 'b) \<longleftrightarrow> is_ceq TYPE('a :: ceq) \<and> is_ceq TYPE('b :: ceq)"
by(simp add: is_ceq_def ceq_prod_def ID_Some ID_None split: option.split)

instantiation list :: (ceq) ceq begin
definition "CEQ('a list) = Option.map (\<lambda>eq. (\<lambda>xs ys. list_all2 eq xs ys)) (ID CEQ('a))"
instance
proof
  fix eq
  assume "CEQ('a list) = Some eq"
  then obtain eq_a where a: "ID CEQ('a) = Some eq_a"
    and eq: "\<And>xs ys. eq xs ys \<longleftrightarrow> list_all2 eq_a xs ys"
    by(auto simp add: ceq_list_def)
  from ID_ceq[OF a] show "eq = op ="
    by(simp add: eq[abs_def] list_all2_eq[symmetric, abs_def])
qed
end

lemma is_ceq_list [simp, code_post]:
  "is_ceq TYPE('a list) \<longleftrightarrow> is_ceq TYPE('a :: ceq)"
by(simp add: is_ceq_def ceq_list_def ID_def)

instantiation option :: (ceq) ceq begin
definition "CEQ('a option) =
  Option.map
    (\<lambda>eq. \<lambda>x y. case x of None \<Rightarrow> Option.is_none y 
                | Some x' \<Rightarrow> case y of None \<Rightarrow> False | Some y' \<Rightarrow> eq x' y')
    (ID CEQ('a))"
instance
proof
  fix eq
  assume "CEQ('a option) = Some eq"
  then obtain eq_a where a: "ID CEQ('a) = Some eq_a"
    and eq: "\<And>x y. eq x y \<longleftrightarrow> 
       (case x of None \<Rightarrow> Option.is_none y | Some x' \<Rightarrow> case y of None \<Rightarrow> False | Some y' \<Rightarrow> eq_a x' y')"
    by(auto simp add: ceq_option_def)
  show "eq = op =" by(auto intro!: ext simp add: eq ID_ceq[OF a] Option.is_none_def split: option.splits)
qed
end

lemma is_ceq_option [simp, code_post]:
  "is_ceq TYPE('a option) \<longleftrightarrow> is_ceq TYPE('a :: ceq)"
by(simp add: is_ceq_def ceq_option_def ID_def)

instantiation "fun" :: (type, type) ceq begin
definition "CEQ('a \<Rightarrow> 'b) = None"
instance by(intro_classes)(simp add: ceq_fun_def)
end

lemma is_ceq_fun [simp]: "\<not> is_ceq TYPE('a \<Rightarrow> 'b)"
by(simp add: is_ceq_def ceq_fun_def ID_None)

definition set_eq :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" 
where [code del]: "set_eq = op ="

lemma set_eq_code:
  shows [code]: "set_eq A B \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A"
  and [code_unfold]: "op = = set_eq"
unfolding set_eq_def by blast+

instantiation set :: (ceq) ceq begin
definition "CEQ('a set) = (case ID CEQ('a) of None \<Rightarrow> None | Some _ \<Rightarrow> Some set_eq)"
instance by(intro_classes)(simp add: ceq_set_def set_eq_def split: option.splits)
end

lemma is_ceq_set [simp, code_post]: "is_ceq TYPE('a set) \<longleftrightarrow> is_ceq TYPE('a :: ceq)"
by(simp add: is_ceq_def ceq_set_def ID_None ID_Some split: option.split)

lemma ID_ceq_set_not_None_iff [simp]: "ID CEQ('a set) \<noteq> None \<longleftrightarrow> ID CEQ('a :: ceq) \<noteq> None"
by(simp add: ceq_set_def ID_def split: option.splits)

end
