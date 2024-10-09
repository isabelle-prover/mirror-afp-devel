theory Simple_SACA
  imports 
    "../order/Suffix" 
    "../order/List_Lexorder_Util"
begin

fun gen_suffixes :: "('a :: {linorder,order_bot}) list \<Rightarrow> 'a list list"
  where
"gen_suffixes s = map (suffix s) [0..<(length s)]"

fun suffix_ids :: "('a :: {linorder,order_bot}) list \<Rightarrow> 'a list list \<Rightarrow> nat list"
  where
"suffix_ids s ss = map (\<lambda>x. length s - length x) ss"

fun simple_saca :: "('a :: {linorder,order_bot}) list \<Rightarrow> nat list"
  where
"simple_saca s = suffix_ids s (sort (gen_suffixes s))"

end