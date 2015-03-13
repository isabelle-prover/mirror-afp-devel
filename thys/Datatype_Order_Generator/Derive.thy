section {* Loading derive-commands *}
theory Derive
imports 
  "Comparator_Generator/Compare_Instances"
  "Equality_Generator/Equality_Instances"
  "Hash_Generator/Hash_Instances"
  "Countable_Generator/Countable_Generator"
begin

text{*
We just load the commands to derive comparators, equality-functions, hash functions, and the
command to show that a datatype is countable, so that now all of them are available.
There are further generators available in the AFP entries of lightweight containers and Show.
*}

print_derives

end
