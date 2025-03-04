theory MLTL_Language_Partition_Algorithm

imports Mission_Time_LTL.MLTL_Properties

begin

section \<open>Extended MLTL Data Structure with Interval Compositions\<close>

text \<open> Extended datatype that has an additional nat list associated 
with the temporal operators F, U, R to represent integer compositions 
of the interval\<close>
datatype (atoms_mltl: 'a) mltl_ext =
  True_mltl_ext ("True\<^sub>c") 
| False_mltl_ext ("False\<^sub>c") 
| Prop_mltl_ext 'a ("Prop\<^sub>c '(_')")                           
| Not_mltl_ext "'a mltl_ext" ("Not\<^sub>c _" [85] 85)                    
| And_mltl_ext "'a mltl_ext" "'a mltl_ext" ("_ And\<^sub>c _" [82, 82] 81)           
| Or_mltl_ext "'a mltl_ext" "'a mltl_ext" ("_ Or\<^sub>c _" [81, 81] 80)         
| Future_mltl_ext "nat" "nat" "nat list" "'a mltl_ext" ("F\<^sub>c '[_',_'] '<_'>  _" [88, 88, 88, 88] 87)      
| Global_mltl_ext "nat" "nat" "nat list" "'a mltl_ext" ("G\<^sub>c '[_',_'] '<_'>  _" [88, 88, 88, 88] 87)      
| Until_mltl_ext "'a mltl_ext" "nat" "nat" "nat list" "'a mltl_ext" ("_ U\<^sub>c '[_',_'] '<_'> _" [84, 84, 84, 84] 83)           
| Release_mltl_ext "'a mltl_ext" "nat" "nat" "nat list" "'a mltl_ext" ("_ R\<^sub>c '[_',_'] '<_'> _" [84, 84, 84, 84] 83)   

text \<open>Converts mltl ext formula to mltl by just dropping the nat list\<close>
fun to_mltl:: "'a mltl_ext \<Rightarrow> 'a mltl" where
  "to_mltl True\<^sub>c = True\<^sub>m"
| "to_mltl False\<^sub>c = False\<^sub>m"
| "to_mltl Prop\<^sub>c (p) = Prop\<^sub>m (p)"
| "to_mltl (Not\<^sub>c \<phi>) = Not\<^sub>m (to_mltl \<phi>)"
| "to_mltl (\<phi> And\<^sub>c \<psi>) = (to_mltl \<phi>) And\<^sub>m (to_mltl \<psi>)"
| "to_mltl (\<phi> Or\<^sub>c \<psi>) = (to_mltl \<phi>) Or\<^sub>m (to_mltl \<psi>)"
| "to_mltl (F\<^sub>c [a,b] <L> \<phi>) = (F\<^sub>m [a,b] (to_mltl \<phi>))"
| "to_mltl (G\<^sub>c [a,b] <L> \<phi>) = (G\<^sub>m [a,b] (to_mltl \<phi>))"
| "to_mltl (\<phi> U\<^sub>c [a,b] <L> \<psi>) = ((to_mltl \<phi>) U\<^sub>m [a,b] (to_mltl \<psi>))"
| "to_mltl (\<phi> R\<^sub>c [a,b] <L> \<psi>) = ((to_mltl \<phi>) R\<^sub>m [a,b] (to_mltl \<psi>))"


definition semantics_mltl_ext:: "'a set list \<Rightarrow> 'a mltl_ext \<Rightarrow> bool" 
  ("_ \<Turnstile>\<^sub>c _" [80,80] 80)
  where "\<pi> \<Turnstile>\<^sub>c \<phi> = \<pi> \<Turnstile>\<^sub>m (to_mltl \<phi>)"

definition semantic_equiv_ext:: "'a mltl_ext \<Rightarrow> 'a mltl_ext \<Rightarrow> bool" 
  ("_ \<equiv>\<^sub>c _" [80, 80] 80)
  where "\<phi> \<equiv>\<^sub>c \<psi> = (to_mltl \<phi>) \<equiv>\<^sub>m(to_mltl \<psi>)"

definition language_mltl_r :: "'a mltl \<Rightarrow> nat \<Rightarrow> 'a set list set"
  where "language_mltl_r \<phi> r = 
  {\<pi>. semantics_mltl \<pi> \<phi> \<and> length \<pi> \<ge> r}"

fun convert_nnf_ext:: "'a mltl_ext \<Rightarrow> 'a mltl_ext" where
  "convert_nnf_ext True\<^sub>c = True\<^sub>c"
  | "convert_nnf_ext False\<^sub>c = False\<^sub>c"
  | "convert_nnf_ext Prop\<^sub>c (p) = Prop\<^sub>c (p)"
  | "convert_nnf_ext (\<phi> And\<^sub>c \<psi>) = ((convert_nnf_ext \<phi>) And\<^sub>c (convert_nnf_ext \<psi>))"
  | "convert_nnf_ext (\<phi> Or\<^sub>c \<psi>) = ((convert_nnf_ext \<phi>) Or\<^sub>c (convert_nnf_ext \<psi>))"
  | "convert_nnf_ext (F\<^sub>c [a,b] <L> \<phi>) = (F\<^sub>c [a,b] <L> (convert_nnf_ext \<phi>))"
  | "convert_nnf_ext (G\<^sub>c [a,b] <L> \<phi>) = (G\<^sub>c [a,b] <L> (convert_nnf_ext \<phi>))"
  | "convert_nnf_ext (\<phi> U\<^sub>c [a,b] <L> \<psi>) = ((convert_nnf_ext \<phi>) U\<^sub>c [a,b] <L> (convert_nnf_ext \<psi>))"
  | "convert_nnf_ext (\<phi> R\<^sub>c [a,b] <L> \<psi>) = ((convert_nnf_ext \<phi>) R\<^sub>c [a,b] <L> (convert_nnf_ext \<psi>))"
  (* Rewriting with logical duals *)
  | "convert_nnf_ext (Not\<^sub>c True\<^sub>c) = False\<^sub>c" 
  | "convert_nnf_ext (Not\<^sub>c False\<^sub>c) = True\<^sub>c" 
  | "convert_nnf_ext (Not\<^sub>c Prop\<^sub>c (p)) = (Not\<^sub>c Prop\<^sub>c (p))"
  | "convert_nnf_ext (Not\<^sub>c (Not\<^sub>c \<phi>)) = convert_nnf_ext \<phi>"
  | "convert_nnf_ext (Not\<^sub>c (\<phi> And\<^sub>c \<psi>)) = ((convert_nnf_ext (Not\<^sub>c \<phi>)) Or\<^sub>c (convert_nnf_ext (Not\<^sub>c \<psi>)))"
  | "convert_nnf_ext (Not\<^sub>c (\<phi> Or\<^sub>c \<psi>)) = ((convert_nnf_ext (Not\<^sub>c \<phi>)) And\<^sub>c (convert_nnf_ext (Not\<^sub>c \<psi>)))"
  | "convert_nnf_ext (Not\<^sub>c (F\<^sub>c [a,b] <L> \<phi>)) = (G\<^sub>c [a,b] <L> (convert_nnf_ext (Not\<^sub>c \<phi>)))"
  | "convert_nnf_ext (Not\<^sub>c (G\<^sub>c [a,b] <L> \<phi>)) = (F\<^sub>c [a,b] <L> (convert_nnf_ext (Not\<^sub>c \<phi>)))"
  | "convert_nnf_ext (Not\<^sub>c (\<phi> U\<^sub>c [a,b] <L> \<psi>)) = ((convert_nnf_ext (Not\<^sub>c \<phi>)) R\<^sub>c [a,b] <L> (convert_nnf_ext (Not\<^sub>c \<psi>)))"
  | "convert_nnf_ext (Not\<^sub>c (\<phi> R\<^sub>c [a,b] <L> \<psi>)) = ((convert_nnf_ext (Not\<^sub>c \<phi>)) U\<^sub>c [a,b] <L> (convert_nnf_ext (Not\<^sub>c \<psi>)))"


section \<open>List Helper Functions and Properties\<close>
text \<open>Computes the partial sum of the first i elements of list\<close>
definition partial_sum :: "[nat list, nat] \<Rightarrow> nat" where
  "partial_sum L i = sum_list (take i L)"

text \<open>Given interval start time a, and a list of ints L = [t1, t2, t3]
Constructs the list (of length 1 longer) of partial sums added to a:
  [a, a+t1, a+t1+t2, a+t1+t2+t3]\<close>
definition interval_times :: "[nat, nat list] \<Rightarrow> nat list" where
  "interval_times a L = map (\<lambda>i. a + partial_sum L i) [0 ..< length L + 1]"

value "interval_times 3 [1, 2, 3, 4, 5] = 
       [3, 4, 6, 9, 13, 18]"

text \<open>This function checks that L is a composition of n.
A composition of an integer n is a way of writing n 
as the sum of a sequence of (strictly) positive integers\<close>
definition is_composition :: "[nat, nat list] \<Rightarrow> bool" where
  "is_composition n L = ((\<forall>i. List.member L i \<longrightarrow> i > 0) \<and> (sum_list L = n))"

text \<open>Checks that every nat list in input of type mltl ext is a composition of its interval
For example the formula F[2,7] has interval of length 7-2+1=6, and a valid
composition would be L = [2, 3, 1]\<close>
fun is_composition_MLTL:: "'a mltl_ext \<Rightarrow> bool" where
  "is_composition_MLTL (\<phi> And\<^sub>c \<psi>) = ((is_composition_MLTL \<phi>) \<and> (is_composition_MLTL \<psi>))"
| "is_composition_MLTL (\<phi> Or\<^sub>c \<psi>) = ((is_composition_MLTL \<phi>) \<and> (is_composition_MLTL \<psi>))"
| "is_composition_MLTL (G\<^sub>c[a,b] <L> \<phi>) = ((is_composition (b-a+1) L) \<and> (is_composition_MLTL \<phi>))"
| "is_composition_MLTL (Not\<^sub>c \<phi>) = is_composition_MLTL \<phi>"
| "is_composition_MLTL (F\<^sub>c[a,b] <L> \<phi>) = ((is_composition (b-a+1) L) \<and> (is_composition_MLTL \<phi>))"
| "is_composition_MLTL (\<phi> U\<^sub>c[a,b] <L> \<psi>) = ((is_composition (b-a+1) L) \<and> (is_composition_MLTL \<phi>) \<and> (is_composition_MLTL \<psi>))"
| "is_composition_MLTL (\<phi> R\<^sub>c[a,b] <L> \<psi>) = ((is_composition (b-a+1) L) \<and> (is_composition_MLTL \<phi>) \<and> (is_composition_MLTL \<psi>))"
| "is_composition_MLTL _ = True" (*Catches prop, true, false cases*)

definition is_composition_allones:: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "is_composition_allones n L = ((is_composition n L) \<and> (\<forall>i<length L. L!i = 1))"

fun is_composition_MLTL_allones:: "'a mltl_ext \<Rightarrow> bool" where
  "is_composition_MLTL_allones (\<phi> And\<^sub>c \<psi>) = ((is_composition_MLTL_allones \<phi>) \<and> (is_composition_MLTL_allones \<psi>))"
| "is_composition_MLTL_allones (\<phi> Or\<^sub>c \<psi>) = ((is_composition_MLTL_allones \<phi>) \<and> (is_composition_MLTL_allones \<psi>))"
| "is_composition_MLTL_allones (G\<^sub>c[a,b] <L> \<phi>) = ((is_composition_allones (b-a+1) L) \<and> is_composition_MLTL_allones \<phi>)"
| "is_composition_MLTL_allones (Not\<^sub>c \<phi>) = is_composition_MLTL_allones \<phi>"
| "is_composition_MLTL_allones (F\<^sub>c[a,b] <L> \<phi>) = ((is_composition_allones (b-a+1) L) \<and> (is_composition_MLTL_allones \<phi>))"
| "is_composition_MLTL_allones (\<phi> U\<^sub>c[a,b] <L> \<psi>) = ((is_composition_allones (b-a+1) L) \<and> (is_composition_MLTL_allones \<phi>) \<and> (is_composition_MLTL_allones \<psi>))"
| "is_composition_MLTL_allones (\<phi> R\<^sub>c[a,b] <L> \<psi>) = ((is_composition_allones (b-a+1) L) \<and> (is_composition_MLTL_allones \<phi>) \<and> (is_composition_MLTL_allones \<psi>))"
| "is_composition_MLTL_allones _ = True" (*Catches prop, true, false cases*)


section \<open>Decomposition Function\<close>

fun pairs :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a) list" where
  "pairs [] L2 = []"
| "pairs (h1#T1) L2 = (map (\<lambda>x. (h1, x)) L2) @ (pairs T1 L2)"

fun And_mltl_list :: "'a mltl_ext list \<Rightarrow> 'a mltl_ext list \<Rightarrow> 'a mltl_ext list" where
"And_mltl_list D_\<phi> D_\<psi> = map (\<lambda>x. And_mltl_ext (fst x) (snd x)) (pairs D_\<phi> D_\<psi>)"

fun Global_mltl_list :: "'a mltl_ext list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a mltl_ext list" where
"Global_mltl_list D_\<phi> a b L = map (\<lambda>x. Global_mltl_ext a b L x) D_\<phi>"

fun Future_mltl_list :: "'a mltl_ext list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a mltl_ext list" where
"Future_mltl_list D_\<phi> a b L = map (\<lambda>x. Future_mltl_ext a b L x) D_\<phi>"

fun Until_mltl_list :: "'a mltl_ext \<Rightarrow> 'a mltl_ext list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a mltl_ext list" where
"Until_mltl_list \<phi> D_\<psi> a b L = map (\<lambda>x. Until_mltl_ext \<phi> a b L x) D_\<psi>"

fun Release_mltl_list :: "'a mltl_ext list \<Rightarrow> 'a mltl_ext \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a mltl_ext list" where
"Release_mltl_list D_\<phi> \<psi> a b L = map (\<lambda>x. Release_mltl_ext x a b L \<psi>) D_\<phi>"

fun Mighty_Release_mltl_ext:: "'a mltl_ext \<Rightarrow> 'a mltl_ext \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a mltl_ext"
  where "Mighty_Release_mltl_ext x \<psi> a b L =
             (And_mltl_ext (Release_mltl_ext x a b L \<psi>) 
                           (Future_mltl_ext a b L x))"

fun Mighty_Release_mltl_list :: "'a mltl_ext list \<Rightarrow> 'a mltl_ext \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a mltl_ext list" where
"Mighty_Release_mltl_list D_\<phi> \<psi> a b L = map (\<lambda>x. Mighty_Release_mltl_ext x \<psi> a b L) D_\<phi>"

fun Global_mltl_decomp :: "'a mltl_ext list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a mltl_ext list" where 
  "Global_mltl_decomp D_\<phi> a 0 L = Global_mltl_list D_\<phi> a a [1]"
| "Global_mltl_decomp D_\<phi> a len L = And_mltl_list (Global_mltl_decomp D_\<phi> a (len-1) L) 
   (Global_mltl_list D_\<phi> (a+len) (a+len) [1])"
value "Global_mltl_decomp [True_mltl_ext, (Prop_mltl_ext (0::nat))] 0 2 [3] = 
[(G\<^sub>c [0,0] <[1]>  True\<^sub>c And\<^sub>c G\<^sub>c [1,1] <[1]>  True\<^sub>c) And\<^sub>c G\<^sub>c [2,2] <[1]>  True\<^sub>c,
  (G\<^sub>c [0,0] <[1]>  True\<^sub>c And\<^sub>c G\<^sub>c [1,1] <[1]>  True\<^sub>c) And\<^sub>c G\<^sub>c [2,2] <[1]>  Prop\<^sub>c (0),
  (G\<^sub>c [0,0] <[1]>  True\<^sub>c And\<^sub>c G\<^sub>c [1,1] <[1]>  Prop\<^sub>c (0)) And\<^sub>c G\<^sub>c [2,2] <[1]>  True\<^sub>c,
  (G\<^sub>c [0,0] <[1]>  True\<^sub>c And\<^sub>c G\<^sub>c [1,1] <[1]>  Prop\<^sub>c (0)) And\<^sub>c G\<^sub>c [2,2] <[1]>  Prop\<^sub>c (0),
  (G\<^sub>c [0,0] <[1]>  Prop\<^sub>c (0) And\<^sub>c G\<^sub>c [1,1] <[1]>  True\<^sub>c) And\<^sub>c G\<^sub>c [2,2] <[1]>  True\<^sub>c,
  (G\<^sub>c [0,0] <[1]>  Prop\<^sub>c (0) And\<^sub>c G\<^sub>c [1,1] <[1]>  True\<^sub>c) And\<^sub>c G\<^sub>c [2,2] <[1]>  Prop\<^sub>c (0),
  (G\<^sub>c [0,0] <[1]>  Prop\<^sub>c (0) And\<^sub>c G\<^sub>c [1,1] <[1]>  Prop\<^sub>c (0)) And\<^sub>c G\<^sub>c [2,2] <[1]>  True\<^sub>c,
  (G\<^sub>c [0,0] <[1]>  Prop\<^sub>c (0) And\<^sub>c G\<^sub>c [1,1] <[1]>  Prop\<^sub>c (0)) And\<^sub>c G\<^sub>c [2,2] <[1]>  Prop\<^sub>c (0)]"

fun LP_mltl_aux :: "'a mltl_ext \<Rightarrow> nat \<Rightarrow> 'a mltl_ext list" where 
  "LP_mltl_aux \<phi> 0 = [\<phi>]"
| "LP_mltl_aux True\<^sub>c (Suc k) = [True\<^sub>c]"
| "LP_mltl_aux False\<^sub>c (Suc k) = [False\<^sub>c]"
| "LP_mltl_aux Prop\<^sub>c (p) (Suc k) = [Prop\<^sub>c (p)]"
| "LP_mltl_aux (Not\<^sub>c (Prop\<^sub>c (p))) (Suc k) = [Not\<^sub>c (Prop\<^sub>c (p))]"
| "LP_mltl_aux (\<phi> And\<^sub>c \<psi>) (Suc k)=
   (let D_\<phi> = (LP_mltl_aux (convert_nnf_ext \<phi>) k) in 
   (let D_\<psi> = (LP_mltl_aux (convert_nnf_ext \<psi>) k) in 
   And_mltl_list D_\<phi> D_\<psi>))"
| "LP_mltl_aux (\<phi> Or\<^sub>c \<psi>) (Suc k) = 
   (let D_\<phi> = (LP_mltl_aux (convert_nnf_ext \<phi>) k) in 
   (let D_\<psi> = (LP_mltl_aux (convert_nnf_ext \<psi>) k) in
   (And_mltl_list D_\<phi> D_\<psi>) @ (And_mltl_list [Not\<^sub>c \<phi>] D_\<psi>) @ 
   (And_mltl_list D_\<phi> [(Not\<^sub>c \<psi>)])))"
| "LP_mltl_aux (G\<^sub>c[a,b] <L> \<phi>) (Suc k) = 
   (let D_\<phi> = (LP_mltl_aux (convert_nnf_ext \<phi>) k) in 
   (if (length D_\<phi> \<le> 1) then ([G\<^sub>c[a,b] <L> \<phi>]) 
                         else (Global_mltl_decomp D_\<phi> a (b-a) L)))"
| "LP_mltl_aux (F\<^sub>c[a,b] <L> \<phi>) (Suc k) = 
   (let D_\<phi> = (LP_mltl_aux (convert_nnf_ext \<phi>) k) in 
   (let s = interval_times a L in
   (Future_mltl_list D_\<phi> (s!0) ((s!1)-1) [(s!1)-(s!0)]) @ (concat (map 
    (\<lambda>i. (And_mltl_list [Global_mltl_ext (s!0) ((s!i)-1) [s!i - s!0] (Not\<^sub>c \<phi>)]
    (Future_mltl_list D_\<phi> (s!i) ((s!(i+1))-1) [s!(i+1)-(s!i)])))
    [1 ..< length L]))))"
| "LP_mltl_aux (\<phi> U\<^sub>c[a,b] <L> \<psi>) (Suc k) = 
   (let D_\<psi> = (LP_mltl_aux (convert_nnf_ext \<psi>) k) in 
   (let s = interval_times a L in
   (Until_mltl_list \<phi> D_\<psi> (s!0) ((s!1)-1) [(s!1)-(s!0)]) @ (concat (map
    (\<lambda>i. (And_mltl_list [Global_mltl_ext (s!0) ((s!i)-1) [s!i - s!0] (And_mltl_ext \<phi> (Not\<^sub>c \<psi>))]
                   (Until_mltl_list \<phi> D_\<psi> (s!i) ((s!(i+1)-1)) [s!(i+1)-(s!i)])))
    [1 ..< length L]))))"
| "LP_mltl_aux (\<phi> R\<^sub>c[a,b] <L> \<psi>) (Suc k) = 
   (let D_\<phi> = (LP_mltl_aux (convert_nnf_ext \<phi>) k) in 
   (let s = interval_times a L in 
    [Global_mltl_ext a b L ((Not\<^sub>c \<phi>) And\<^sub>c \<psi>)] @ 
   (Mighty_Release_mltl_list D_\<phi> \<psi> (s!0) ((s!1)-1) [(s!1)-(s!0)]) @ (concat (map
    (\<lambda>i. (And_mltl_list [Global_mltl_ext (s!0) ((s!i)-1) [s!i - s!0] ((Not\<^sub>c \<phi>) And\<^sub>c \<psi>)] 
                   (Mighty_Release_mltl_list D_\<phi> \<psi> (s!i) ((s!(i+1)-1)) [s!(i+1)-(s!i)])))
    [1 ..< length L]))))"
| "LP_mltl_aux _ _ = []"

fun LP_mltl :: "'a mltl_ext \<Rightarrow> nat \<Rightarrow> 'a mltl list" where
"LP_mltl \<phi> k = map (\<lambda>x. to_mltl x) 
(map (\<lambda>x. convert_nnf_ext x) (LP_mltl_aux (convert_nnf_ext \<phi>) k))"


subsection \<open>Examples\<close>

value "LP_mltl_aux (F\<^sub>c[0,9] <[3, 3, 3]> ((Prop\<^sub>c (0::nat)) Or\<^sub>c (Prop\<^sub>c (1::nat)))) 1 =
[F\<^sub>c [0,2] <[3]>  (Prop\<^sub>c (0) Or\<^sub>c Prop\<^sub>c (1)),
 G\<^sub>c [0,2] <[3]>  (Not\<^sub>c (Prop\<^sub>c (0) Or\<^sub>c Prop\<^sub>c (1))) And\<^sub>c F\<^sub>c [3,5] <[3]>  (Prop\<^sub>c (0) Or\<^sub>c Prop\<^sub>c (1)),
 G\<^sub>c [0,5] <[6]>  (Not\<^sub>c (Prop\<^sub>c (0) Or\<^sub>c Prop\<^sub>c (1))) And\<^sub>c F\<^sub>c [6,8] <[3]>  (Prop\<^sub>c (0) Or\<^sub>c Prop\<^sub>c (1))]"

value "LP_mltl (True\<^sub>c Or\<^sub>c (Prop\<^sub>c (0::nat))) 1 =
[True\<^sub>m And\<^sub>m Prop\<^sub>m (0), False\<^sub>m And\<^sub>m Prop\<^sub>m (0), True\<^sub>m And\<^sub>m Not\<^sub>m Prop\<^sub>m (0)]"

value "LP_mltl ((Prop\<^sub>c (0::nat)) U\<^sub>c [2,5] <[4]> (Prop\<^sub>c (1))) 1 =
       [Prop\<^sub>m (0) U\<^sub>m [2,5] Prop\<^sub>m (1)]"

value "LP_mltl ((Prop\<^sub>c (0::nat)) R\<^sub>c[2,5] <[2, 2]> (Prop\<^sub>c (1))) 1 =
[G\<^sub>m [2,5] (Not\<^sub>m Prop\<^sub>m (0) And\<^sub>m Prop\<^sub>m (1)),
  Prop\<^sub>m (0) R\<^sub>m [2,3] Prop\<^sub>m (1) And\<^sub>m F\<^sub>m [2,3] Prop\<^sub>m (0),
  G\<^sub>m [2,3] (Not\<^sub>m Prop\<^sub>m (0) And\<^sub>m Prop\<^sub>m (1)) And\<^sub>m (Prop\<^sub>m (0) R\<^sub>m [4,5] Prop\<^sub>m (1) And\<^sub>m F\<^sub>m [4,5] Prop\<^sub>m (0))]"

value "LP_mltl ((F\<^sub>c[0,3] <[1,1,1,1]> (Prop\<^sub>c (0::nat))) Or\<^sub>c
                (G\<^sub>c[0,3] <[1,1,1,1]> (Prop\<^sub>c (1)))) 3 = 
[F\<^sub>m [0,0] Prop\<^sub>m (0) And\<^sub>m G\<^sub>m [0,3] Prop\<^sub>m (1),
  (G\<^sub>m [0,0] (Not\<^sub>m Prop\<^sub>m (0)) And\<^sub>m F\<^sub>m [1,1] Prop\<^sub>m (0)) And\<^sub>m G\<^sub>m [0,3] Prop\<^sub>m (1),
  (G\<^sub>m [0,1] (Not\<^sub>m Prop\<^sub>m (0)) And\<^sub>m F\<^sub>m [2,2] Prop\<^sub>m (0)) And\<^sub>m G\<^sub>m [0,3] Prop\<^sub>m (1),
  (G\<^sub>m [0,2] (Not\<^sub>m Prop\<^sub>m (0)) And\<^sub>m F\<^sub>m [3,3] Prop\<^sub>m (0)) And\<^sub>m G\<^sub>m [0,3] Prop\<^sub>m (1),
  G\<^sub>m [0,3] (Not\<^sub>m Prop\<^sub>m (0)) And\<^sub>m G\<^sub>m [0,3] Prop\<^sub>m (1),
  F\<^sub>m [0,0] Prop\<^sub>m (0) And\<^sub>m F\<^sub>m [0,3] (Not\<^sub>m Prop\<^sub>m (1)),
  (G\<^sub>m [0,0] (Not\<^sub>m Prop\<^sub>m (0)) And\<^sub>m F\<^sub>m [1,1] Prop\<^sub>m (0)) And\<^sub>m F\<^sub>m [0,3] (Not\<^sub>m Prop\<^sub>m (1)),
  (G\<^sub>m [0,1] (Not\<^sub>m Prop\<^sub>m (0)) And\<^sub>m F\<^sub>m [2,2] Prop\<^sub>m (0)) And\<^sub>m F\<^sub>m [0,3] (Not\<^sub>m Prop\<^sub>m (1)),
  (G\<^sub>m [0,2] (Not\<^sub>m Prop\<^sub>m (0)) And\<^sub>m F\<^sub>m [3,3] Prop\<^sub>m (0)) And\<^sub>m F\<^sub>m [0,3] (Not\<^sub>m Prop\<^sub>m (1))]"

end
