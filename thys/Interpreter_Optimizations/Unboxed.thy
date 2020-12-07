theory Unboxed
  imports Global Dynamic
begin

datatype type = Bool | Num

datatype 'dyn unboxed =
  is_dyn_operand: OpDyn 'dyn |
  OpNum nat |
  OpBool bool

fun typeof where
  "typeof (OpDyn _) = None" |
  "typeof (OpNum _) = Some Num" |
  "typeof (OpBool _) = Some Bool"

fun cast_Dyn :: "'dyn unboxed \<Rightarrow> 'dyn option" where
  "cast_Dyn (OpDyn d) = Some d" |
  "cast_Dyn _ = None"

fun cast_Num :: "'dyn unboxed \<Rightarrow> nat option" where
  "cast_Num (OpNum n) = Some n" |
  "cast_Num _ = None"

fun cast_Bool :: "'dyn unboxed \<Rightarrow> bool option" where
  "cast_Bool (OpBool b) = Some b" |
  "cast_Bool _ = None"

locale unboxedval = dynval is_true is_false
  for is_true :: "'dyn \<Rightarrow> bool" and is_false +
  fixes
    box_num :: "nat \<Rightarrow> 'dyn" and unbox_num :: "'dyn \<Rightarrow> nat option" and
    box_bool :: "bool \<Rightarrow> 'dyn" and unbox_bool :: "'dyn \<Rightarrow> bool option"
  assumes
    box_unbox_inverse_num: "unbox_num d = Some n \<Longrightarrow> box_num n = d" and
    box_unbox_inverse_bool: "unbox_bool d = Some b \<Longrightarrow> box_bool b = d"
begin

fun unbox :: "type \<Rightarrow> 'dyn \<Rightarrow> 'dyn unboxed option" where
  "unbox Num = map_option OpNum \<circ> unbox_num" |
  "unbox Bool = map_option OpBool \<circ> unbox_bool"

fun cast_and_box :: "type \<Rightarrow> 'dyn unboxed \<Rightarrow> 'dyn option" where
  "cast_and_box Num = map_option box_num \<circ> cast_Num" |
  "cast_and_box Bool = map_option box_bool \<circ> cast_Bool"

fun norm_unboxed :: "'dyn unboxed \<Rightarrow> 'dyn" where
  "norm_unboxed (OpDyn d) = d" |
  "norm_unboxed (OpNum n) = box_num n" |
  "norm_unboxed (OpBool b) = box_bool b"

fun box_operand :: "'dyn unboxed \<Rightarrow> 'dyn unboxed" where
  "box_operand (OpDyn d) = OpDyn d" |
  "box_operand (OpNum n) = OpDyn (box_num n)" |
  "box_operand (OpBool b) = OpDyn (box_bool b)"

fun box_frame where
  "box_frame f (Frame g pc \<Sigma>) = Frame g pc (if f = g then map box_operand \<Sigma> else \<Sigma>)"

definition box_stack where
  "box_stack f \<equiv> map (box_frame f)"

end

end