section\<open>Converting Types to Strings and Back Again\<close>
theory ReadShow
  imports 
    Solidity_Symbex 
begin 

text\<open>
  In the following, we formalize a family of projection (and injection) functions for injecting 
  (projecting) basic types (i.e., @{type \<open>nat\<close>}, @{type \<open>int\<close>}, and @{type \<open>bool\<close>} in (out) of the 
  domains of strings. We provide variants for the two string representations of Isabelle/HOL, namely
  @{type \<open>string\<close>} and @{type \<open>String.literal\<close>}. 
\<close>


subsubsection\<open>Bool\<close>
definition 
 \<open>Read\<^sub>b\<^sub>o\<^sub>o\<^sub>l s = (if s = ''True'' then True else False)\<close>
definition
 \<open>Show\<^sub>b\<^sub>o\<^sub>o\<^sub>l b = (if b then ''True'' else ''False'')\<close>
definition 
 \<open>STR_is_bool s = (Show\<^sub>b\<^sub>o\<^sub>o\<^sub>l (Read\<^sub>b\<^sub>o\<^sub>o\<^sub>l s) = s)\<close>

declare Read\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def [solidity_symbex]
        Show\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def [solidity_symbex]

lemma Show_Read_bool_id: \<open>STR_is_bool s \<Longrightarrow> (Show\<^sub>b\<^sub>o\<^sub>o\<^sub>l (Read\<^sub>b\<^sub>o\<^sub>o\<^sub>l s) = s)\<close>
  using STR_is_bool_def by fastforce

lemma STR_is_bool_split: \<open>STR_is_bool s \<Longrightarrow> s = ''False'' \<or> s = ''True''\<close>
  by(auto simp: STR_is_bool_def Read\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def Show\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def)

lemma Read_Show_bool_id: \<open>Read\<^sub>b\<^sub>o\<^sub>o\<^sub>l (Show\<^sub>b\<^sub>o\<^sub>o\<^sub>l b) = b\<close>
  by(auto simp: Read\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def Show\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def)

definition ReadL\<^sub>b\<^sub>o\<^sub>o\<^sub>l::\<open>String.literal \<Rightarrow> bool\<close> (\<open>\<lfloor>_\<rfloor>\<close>) where 
 \<open>ReadL\<^sub>b\<^sub>o\<^sub>o\<^sub>l s = (if s = STR ''True'' then True else False)\<close>
definition ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l:: \<open>bool \<Rightarrow> String.literal\<close> (\<open>\<lceil>_\<rceil>\<close>) where
 \<open>ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l b = (if b then STR ''True'' else STR ''False'')\<close>
definition 
 \<open>strL_is_bool' s = (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l (ReadL\<^sub>b\<^sub>o\<^sub>o\<^sub>l s) = s)\<close>

declare ReadL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def [solidity_symbex]
        ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def [solidity_symbex]


lemma Show_Read_bool'_id: \<open>strL_is_bool' s \<Longrightarrow> (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l (ReadL\<^sub>b\<^sub>o\<^sub>o\<^sub>l s) = s)\<close>
  using strL_is_bool'_def by fastforce

lemma strL_is_bool'_split:  \<open>strL_is_bool' s \<Longrightarrow> s = STR ''False'' \<or> s = STR ''True''\<close>
  by(auto simp: strL_is_bool'_def ReadL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def)

lemma Read_Show_bool'_id[simp]: \<open>ReadL\<^sub>b\<^sub>o\<^sub>o\<^sub>l (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l b) = b\<close>
  by(auto simp: ReadL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def)

lemma true_neq_false[simp]: "ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True \<noteq> ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False"
  by (metis Read_Show_bool'_id)

subsubsection\<open>Natural Numbers\<close>

definition  nat_of_digit ::  \<open>char \<Rightarrow> nat\<close> where
  \<open>nat_of_digit c = 
    (if c = CHR ''0'' then 0
    else if c = CHR ''1'' then 1
    else if c = CHR ''2'' then 2
    else if c = CHR ''3'' then 3
    else if c = CHR ''4'' then 4
    else if c = CHR ''5'' then 5
    else if c = CHR ''6'' then 6
    else if c = CHR ''7'' then 7
    else if c = CHR ''8'' then 8
    else if c = CHR ''9'' then 9
    else undefined)\<close>

declare nat_of_digit_def [solidity_symbex]

definition  is_digit ::  \<open>char \<Rightarrow> bool\<close> where
 \<open>is_digit c = 
    (if c = CHR ''0'' then True
    else if c = CHR ''1'' then True
    else if c = CHR ''2'' then True
    else if c = CHR ''3'' then True
    else if c = CHR ''4'' then True
    else if c = CHR ''5'' then True
    else if c = CHR ''6'' then True
    else if c = CHR ''7'' then True
    else if c = CHR ''8'' then True
    else if c = CHR ''9'' then True
    else if c = CHR ''-'' then True
    else False)\<close>



definition  digit_of_nat ::  \<open>nat \<Rightarrow> char\<close> where
  \<open>digit_of_nat x =
    (if x = 0 then CHR ''0''
    else if x = 1 then CHR ''1''
    else if x = 2 then CHR ''2''
    else if x = 3 then CHR ''3''
    else if x = 4 then CHR ''4''
    else if x = 5 then CHR ''5''
    else if x = 6 then CHR ''6''
    else if x = 7 then CHR ''7''
    else if x = 8 then CHR ''8''
    else if x = 9 then CHR ''9''
    else undefined)\<close>

declare digit_of_nat_def [solidity_symbex]

lemma nat_of_digit_digit_of_nat_id: 
    \<open>x < 10 \<Longrightarrow> nat_of_digit (digit_of_nat x) = x\<close>
  by(simp add:nat_of_digit_def digit_of_nat_def)

lemma img_digit_of_nat: 
\<open>n < 10 \<Longrightarrow> digit_of_nat n \<in> {CHR ''0'', CHR ''1'', CHR ''2'', CHR ''3'', CHR ''4'',
                              CHR ''5'', CHR ''6'', CHR ''7'', CHR ''8'', CHR ''9''}\<close>
  by(simp add:nat_of_digit_def digit_of_nat_def)

lemma digit_of_nat_nat_of_digit_id: 
    \<open>c \<in> {CHR ''0'', CHR ''1'', CHR ''2'', CHR ''3'', CHR ''4'',
          CHR ''5'', CHR ''6'', CHR ''7'', CHR ''8'', CHR ''9''} 
      \<Longrightarrow> digit_of_nat (nat_of_digit c) = c\<close>
  by(code_simp, auto) 

definition 
  nat_implode :: \<open>'a::{numeral,power,zero} list \<Rightarrow> 'a\<close> where
 \<open>nat_implode n = foldr (+) (map (\<lambda> (p,d) \<Rightarrow> 10 ^ p * d) (enumerate 0 (rev n))) 0\<close>

declare nat_implode_def [solidity_symbex]

fun nat_explode' :: \<open>nat \<Rightarrow> nat list\<close> where 
   \<open>nat_explode' x = (case  x < 10 of True \<Rightarrow> [x mod 10] 
                                       | _ \<Rightarrow> (x mod 10 )#(nat_explode' (x div 10)))\<close>

definition 
  nat_explode :: \<open>nat \<Rightarrow> nat list\<close> where
 \<open>nat_explode x = (rev (nat_explode' x))\<close>

declare nat_explode_def [solidity_symbex]

lemma nat_explode'_not_empty: \<open>nat_explode' n \<noteq> []\<close> 
  by (smt (z3) list.simps(3) nat_explode'.simps) 

lemma nat_explode_not_empty: \<open>nat_explode n \<noteq> []\<close>
  using nat_explode'_not_empty nat_explode_def by auto 

lemma nat_explode'_ne_suc: \<open>\<exists> n. nat_explode' (Suc n) \<noteq> nat_explode' n\<close>
  by(rule exI [of _ \<open>0::nat\<close>], simp)

lemma nat_explode'_digit: \<open>hd (nat_explode' n ) < 10\<close>
proof(induct  \<open>n\<close>)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case proof (cases \<open>n < 9\<close>)
    case True
    then show ?thesis by simp 
  next
    case False
    then show ?thesis 
      by simp
  qed
qed

lemma div_ten_less: \<open>n \<noteq> 0 \<Longrightarrow> ((n::nat) div 10) < n\<close>
  by simp

lemma unroll_nat_explode': 
 \<open>\<not> n < 10 \<Longrightarrow> (case n < 10 of True \<Rightarrow> [n mod 10] | False \<Rightarrow> n mod 10 # nat_explode' (n div 10)) =
       (n mod 10 # nat_explode' (n div 10))\<close>
  by simp

lemma nat_explode_mod_10_ident: \<open>map (\<lambda> x. x mod 10) (nat_explode' n) = nat_explode' n\<close>
proof (cases \<open>n < 10\<close>)
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis 
  proof (induct \<open>n\<close> rule: nat_less_induct)
  case (1 n) note * = this
  then show ?case 
    using div_ten_less apply(simp (no_asm))  
    using unroll_nat_explode'[of n] * 
    by (smt (z3) list.simps(8) list.simps(9) mod_div_trivial mod_eq_self_iff_div_eq_0 
                 nat_explode'.simps zero_less_numeral)
  qed
qed

lemma nat_explode'_digits:
  \<open>\<forall>d \<in> set (nat_explode' n). d < 10\<close>
proof
  fix d
  assume \<open>d \<in> set (nat_explode' n)\<close>
  then have \<open>d \<in> set (map (\<lambda>m. m mod 10) (nat_explode' n))\<close>
    by (simp only: nat_explode_mod_10_ident)
  then show \<open>d < 10\<close>
    by auto
qed

lemma nat_explode_digits:
  \<open>\<forall>d \<in> set (nat_explode n). d < 10\<close>
  using nat_explode'_digits [of n] by (simp only: nat_explode_def set_rev)

value \<open>nat_implode(nat_explode 42) = 42\<close>
value \<open>nat_explode (Suc 21)\<close>


lemma nat_implode_append: 
 \<open>nat_implode (a@[b]) = (1*b + foldr (+) (map (\<lambda>(p, y). 10 ^ p * y) (enumerate (Suc 0) (rev a))) 0 )\<close>
  by(simp add:nat_implode_def)

lemma enumerate_suc: \<open>enumerate (Suc n) l = map (\<lambda> (a,b). (a+1::nat,b)) (enumerate n l)\<close>
proof (induction \<open>l\<close>)
  case Nil
  then show ?case by simp
next
  case (Cons a x) note * = this
  then show ?case apply(simp only:enumerate_simps)
    
    apply(simp only:\<open>enumerate (Suc n) x = map (\<lambda>a. case a of (a, b) \<Rightarrow> (a + 1, b)) (enumerate n x)\<close>[symmetric])
    apply(simp)
    using *
    by (metis apfst_conv cond_case_prod_eta enumerate_Suc_eq)
qed

lemma mult_assoc_aux1: 
 \<open>(\<lambda>(p, y). 10 ^ p * y) \<circ> (\<lambda>(a, y). (Suc a, y)) = (\<lambda>(p, y). (10::nat) * (10 ^ p) * y)\<close>
  by(auto simp:o_def)

lemma fold_map_transfer: 
 \<open>(foldr (+) (map (\<lambda>(x,y). 10 * (f (x,y))) l) (0::nat)) = 10 * (foldr (+) (map (\<lambda>x. (f x)) l) (0::nat))\<close>
proof(induct \<open>l\<close>)            
  case Nil
  then show ?case by(simp)
next
  case (Cons a l)
  then show ?case  by(simp)
qed 

lemma mult_assoc_aux2: \<open>(\<lambda>(p, y). 10 * 10 ^ p * (y::nat)) = (\<lambda>(p, y). 10 * (10 ^ p * y))\<close>
  by(auto)

lemma nat_implode_explode_id: \<open>nat_implode (nat_explode n) = n\<close>
proof (cases \<open>n=0\<close>) 
  case True note * = this
  then show ?thesis 
    by (simp add: nat_explode_def nat_implode_def) 
next
  case False
  then show ?thesis 
  proof (induct \<open>n\<close> rule: nat_less_induct)
    case (1 n) note * = this
    then  have 
      **: \<open>nat_implode (nat_explode (n div 10)) = n div 10\<close>
    proof (cases \<open>n div 10 = 0\<close>) 
      case True 
      then show ?thesis by(simp add: nat_explode_def nat_implode_def)
    next
      case False
      then show ?thesis 
      using div_ten_less[of \<open>n\<close>] * 
      by(simp)      
  qed
    then show ?case  
    proof (cases \<open>n < 10\<close>)
      case True
      then show ?thesis  by(simp add: nat_explode_def nat_implode_def)
    next 
      case False note *** = this
      then show ?thesis 
        apply(simp (no_asm)  add:nat_explode_def del:rev_rev_ident)
        apply(simp only: bool.case(2))
        apply(simp del:nat_explode'.simps rev_rev_ident)
        apply(fold nat_explode_def)
        apply(simp only:nat_implode_append)
        apply(simp add:enumerate_suc)
        apply(simp only:mult_assoc_aux1) 
        using mult_assoc_aux2 apply(simp)
        using fold_map_transfer[of \<open>\<lambda>(p, y). 10 ^ p * y\<close> 
                                   \<open>(enumerate 0 (rev (nat_explode (n div 10))))\<close>, simplified]
        apply(simp) apply(fold nat_implode_def) using ** 
        by simp
      qed
  qed
qed

definition 
  Read\<^sub>n\<^sub>a\<^sub>t :: \<open>string \<Rightarrow> nat\<close> where 
 \<open>Read\<^sub>n\<^sub>a\<^sub>t s = nat_implode (map nat_of_digit s)\<close>

definition 
  Show\<^sub>n\<^sub>a\<^sub>t::"nat \<Rightarrow> string" where
 \<open>Show\<^sub>n\<^sub>a\<^sub>t n = map digit_of_nat (nat_explode n)\<close>

declare Read\<^sub>n\<^sub>a\<^sub>t_def [solidity_symbex]
        Show\<^sub>n\<^sub>a\<^sub>t_def [solidity_symbex]

definition 
  \<open>STR_is_nat s = (Show\<^sub>n\<^sub>a\<^sub>t (Read\<^sub>n\<^sub>a\<^sub>t s) = s)\<close>

value \<open>Read\<^sub>n\<^sub>a\<^sub>t ''10''\<close>
value \<open>Show\<^sub>n\<^sub>a\<^sub>t 10\<close>
value \<open>Read\<^sub>n\<^sub>a\<^sub>t (Show\<^sub>n\<^sub>a\<^sub>t (10)) = 10\<close>
value \<open>Show\<^sub>n\<^sub>a\<^sub>t (Read\<^sub>n\<^sub>a\<^sub>t (''10'')) = ''10''\<close>

lemma Show_nat_not_neg: 
  \<open>set (Show\<^sub>n\<^sub>a\<^sub>t n) \<subseteq>{CHR ''0'', CHR ''1'', CHR ''2'', CHR ''3'', CHR ''4'',
                     CHR ''5'', CHR ''6'', CHR ''7'', CHR ''8'', CHR ''9''}\<close>
  unfolding Show\<^sub>n\<^sub>a\<^sub>t_def
  using  nat_explode_digits[of n]  img_digit_of_nat imageE image_set subsetI
  by (smt (verit) imageE image_set subsetI)

lemma Show_nat_not_empty: \<open>(Show\<^sub>n\<^sub>a\<^sub>t n) \<noteq> []\<close>
  by (simp add: Show\<^sub>n\<^sub>a\<^sub>t_def nat_explode_not_empty)

lemma not_hd: \<open>L \<noteq> [] \<Longrightarrow> e \<notin> set(L) \<Longrightarrow> hd L \<noteq> e\<close>
  by auto

lemma Show_nat_not_neg'': \<open>hd (Show\<^sub>n\<^sub>a\<^sub>t n) \<noteq> (CHR ''-'')\<close>
  using Show_nat_not_neg[of \<open>n\<close>]
  Show_nat_not_empty[of \<open>n\<close>] not_hd[of \<open>Show\<^sub>n\<^sub>a\<^sub>t n\<close>]
  by auto

lemma Show_Read_nat_id: \<open>STR_is_nat s \<Longrightarrow> (Show\<^sub>n\<^sub>a\<^sub>t (Read\<^sub>n\<^sub>a\<^sub>t s) = s)\<close>
  by(simp add:STR_is_nat_def)

lemma bar': \<open>\<forall> d \<in> set l . d < 10 \<Longrightarrow> map nat_of_digit (map digit_of_nat l) = l\<close>
  using  nat_of_digit_digit_of_nat_id 
  by (simp add: map_idI)

lemma Read_Show_nat_id: \<open>Read\<^sub>n\<^sub>a\<^sub>t(Show\<^sub>n\<^sub>a\<^sub>t n) = n\<close>
  apply(unfold Read\<^sub>n\<^sub>a\<^sub>t_def Show\<^sub>n\<^sub>a\<^sub>t_def)
  using bar' nat_of_digit_digit_of_nat_id nat_explode_digits
  using nat_implode_explode_id 
  by presburger

definition 
  ReadL\<^sub>n\<^sub>a\<^sub>t :: \<open>String.literal \<Rightarrow> nat\<close> (\<open>\<lceil>_\<rceil>\<close>) where 
 \<open>ReadL\<^sub>n\<^sub>a\<^sub>t = Read\<^sub>n\<^sub>a\<^sub>t \<circ> String.explode\<close>

definition 
  ShowL\<^sub>n\<^sub>a\<^sub>t::\<open>nat \<Rightarrow> String.literal\<close> (\<open>\<lfloor>_\<rfloor>\<close>)where
 \<open>ShowL\<^sub>n\<^sub>a\<^sub>t = String.implode \<circ> Show\<^sub>n\<^sub>a\<^sub>t\<close>

declare ReadL\<^sub>n\<^sub>a\<^sub>t_def [solidity_symbex]
        ShowL\<^sub>n\<^sub>a\<^sub>t_def [solidity_symbex]


definition 
  \<open>strL_is_nat' s = (ShowL\<^sub>n\<^sub>a\<^sub>t (ReadL\<^sub>n\<^sub>a\<^sub>t s) = s)\<close>

value \<open>\<lceil>STR ''10''\<rceil>::nat\<close>
value \<open>ReadL\<^sub>n\<^sub>a\<^sub>t (STR ''10'')\<close>
value \<open>\<lfloor>10::nat\<rfloor>\<close>
value \<open>ShowL\<^sub>n\<^sub>a\<^sub>t 10\<close>
value \<open>ReadL\<^sub>n\<^sub>a\<^sub>t (ShowL\<^sub>n\<^sub>a\<^sub>t (10)) = 10\<close>
value \<open>ShowL\<^sub>n\<^sub>a\<^sub>t (ReadL\<^sub>n\<^sub>a\<^sub>t (STR ''10'')) = STR ''10''\<close>

lemma Show_Read_nat'_id: \<open>strL_is_nat' s \<Longrightarrow> (ShowL\<^sub>n\<^sub>a\<^sub>t (ReadL\<^sub>n\<^sub>a\<^sub>t s) = s)\<close>
  by(simp add:strL_is_nat'_def)

lemma digits_are_ascii: 
  \<open>c \<in> {CHR ''0'', CHR ''1'', CHR ''2'', CHR ''3'', CHR ''4'', 
        CHR ''5'', CHR ''6'', CHR ''7'', CHR ''8'', CHR ''9''}
   \<Longrightarrow> String.ascii_of c = c\<close>
  by auto

lemma Show\<^sub>n\<^sub>a\<^sub>t_ascii: \<open>map String.ascii_of (Show\<^sub>n\<^sub>a\<^sub>t n) = Show\<^sub>n\<^sub>a\<^sub>t n\<close>
  using Show_nat_not_neg digits_are_ascii
  by (meson map_idI subsetD)


lemma Read_Show_nat'_id: \<open>ReadL\<^sub>n\<^sub>a\<^sub>t(ShowL\<^sub>n\<^sub>a\<^sub>t n) = n\<close>
  apply(unfold ReadL\<^sub>n\<^sub>a\<^sub>t_def ShowL\<^sub>n\<^sub>a\<^sub>t_def, simp)
  by (simp add: Show\<^sub>n\<^sub>a\<^sub>t_ascii  Read_Show_nat_id)


subsubsection\<open>Integer\<close>
definition 
  Read\<^sub>i\<^sub>n\<^sub>t :: \<open>string \<Rightarrow> int\<close> where 
 \<open>Read\<^sub>i\<^sub>n\<^sub>t x = (if hd x = (CHR ''-'') then  -(int (Read\<^sub>n\<^sub>a\<^sub>t (tl x))) else int (Read\<^sub>n\<^sub>a\<^sub>t x))\<close>

definition 
  Show\<^sub>i\<^sub>n\<^sub>t::\<open>int \<Rightarrow> string\<close> where
 \<open>Show\<^sub>i\<^sub>n\<^sub>t i = (if i < 0 then (CHR ''-'')#(Show\<^sub>n\<^sub>a\<^sub>t (nat (-i))) 
                        else Show\<^sub>n\<^sub>a\<^sub>t (nat i))\<close>

definition 
 \<open>STR_is_int s = (Show\<^sub>i\<^sub>n\<^sub>t (Read\<^sub>i\<^sub>n\<^sub>t s) = s)\<close>


declare Read\<^sub>i\<^sub>n\<^sub>t_def [solidity_symbex]
        Show\<^sub>i\<^sub>n\<^sub>t_def [solidity_symbex]

value \<open>Read\<^sub>i\<^sub>n\<^sub>t (Show\<^sub>i\<^sub>n\<^sub>t   10)  =  10\<close>
value \<open>Read\<^sub>i\<^sub>n\<^sub>t (Show\<^sub>i\<^sub>n\<^sub>t (-10)) = -10\<close>

value \<open>Show\<^sub>i\<^sub>n\<^sub>t (Read\<^sub>i\<^sub>n\<^sub>t (''10''))  =  ''10''\<close>
value \<open>Show\<^sub>i\<^sub>n\<^sub>t (Read\<^sub>i\<^sub>n\<^sub>t (''-10'')) = ''-10''\<close>

lemma Show_Read_id: \<open>STR_is_int s \<Longrightarrow> (Show\<^sub>i\<^sub>n\<^sub>t (Read\<^sub>i\<^sub>n\<^sub>t s) = s)\<close>
  by(simp add:STR_is_int_def)
                          
lemma Read_Show_id: \<open>Read\<^sub>i\<^sub>n\<^sub>t(Show\<^sub>i\<^sub>n\<^sub>t(x)) = x\<close>
  apply(code_simp)
  apply(auto simp:Show_nat_not_neg Read_Show_nat_id)[1]
  apply(thin_tac \<open>\<not> x < 0 \<close>)
  using Show_nat_not_neg''
  by blast 

lemma STR_is_int_Show: \<open>STR_is_int (Show\<^sub>i\<^sub>n\<^sub>t n)\<close>
  by(simp add:STR_is_int_def Read_Show_id)

definition 
  ReadL\<^sub>i\<^sub>n\<^sub>t :: \<open>String.literal \<Rightarrow> int\<close> (\<open>\<lceil>_\<rceil>\<close>) where 
 \<open>ReadL\<^sub>i\<^sub>n\<^sub>t  = Read\<^sub>i\<^sub>n\<^sub>t \<circ> String.explode\<close> 

definition 
  ShowL\<^sub>i\<^sub>n\<^sub>t::\<open>int \<Rightarrow> String.literal\<close> (\<open>\<lfloor>_\<rfloor>\<close>) where
 \<open>ShowL\<^sub>i\<^sub>n\<^sub>t =String.implode \<circ> Show\<^sub>i\<^sub>n\<^sub>t\<close>

definition 
 \<open>strL_is_int' s = (ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t s) = s)\<close>

declare ReadL\<^sub>i\<^sub>n\<^sub>t_def [solidity_symbex]
        ShowL\<^sub>i\<^sub>n\<^sub>t_def [solidity_symbex]

value \<open>ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t   10)  =  10\<close>
value \<open>ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t (-10)) = -10\<close>

value \<open>ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (STR ''10''))  =  STR ''10''\<close>
value \<open>ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (STR ''-10'')) = STR ''-10''\<close>

lemma Show_ReadL_id: \<open>strL_is_int' s \<Longrightarrow> (ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t s) = s)\<close>
  by(simp add:strL_is_int'_def)

lemma Read_ShowL_id: \<open>ReadL\<^sub>i\<^sub>n\<^sub>t (ShowL\<^sub>i\<^sub>n\<^sub>t x) = x\<close>
proof(cases \<open>x < 0\<close>)
  case True
  then show ?thesis using ShowL\<^sub>i\<^sub>n\<^sub>t_def ReadL\<^sub>i\<^sub>n\<^sub>t_def Show\<^sub>i\<^sub>n\<^sub>t_def Show\<^sub>n\<^sub>a\<^sub>t_ascii 
    by (metis (no_types, lifting) Read_Show_id String.ascii_of_Char comp_def implode.rep_eq list.simps(9)) 
next
  case False
  then show ?thesis using ShowL\<^sub>i\<^sub>n\<^sub>t_def ReadL\<^sub>i\<^sub>n\<^sub>t_def Show\<^sub>i\<^sub>n\<^sub>t_def Show\<^sub>n\<^sub>a\<^sub>t_ascii 
    by (metis Read_Show_id String.explode_implode_eq comp_apply)
qed 

lemma STR_is_int_ShowL: \<open>strL_is_int' (ShowL\<^sub>i\<^sub>n\<^sub>t n)\<close>
  by(simp add:strL_is_int'_def Read_ShowL_id)

lemma String_Cancel: "a + (c::String.literal) = b + c \<Longrightarrow> a = b"
using String.plus_literal.rep_eq
by (metis append_same_eq literal.explode_inject)

end
                                            
