theory Idle_Aux
imports Idle Stack_Aux
begin

fun list :: "'a idle \<Rightarrow> 'a list" where
  "list (Idle stack _) = Stack_Aux.list stack"

instantiation idle :: (type) size
begin

fun size_idle :: "'a idle \<Rightarrow> nat" where
  "size (Idle stack _) = size stack"

instance..
end

instantiation idle :: (type) is_empty
begin

fun is_empty_idle :: "'a idle \<Rightarrow> bool" where
  "is_empty (Idle stack _) \<longleftrightarrow> is_empty stack"

instance..
end

instantiation idle ::(type) invar
begin

fun invar_idle :: "'a idle \<Rightarrow> bool" where
  "invar (Idle stack stackSize) \<longleftrightarrow> size stack = stackSize"

instance..
end

end
