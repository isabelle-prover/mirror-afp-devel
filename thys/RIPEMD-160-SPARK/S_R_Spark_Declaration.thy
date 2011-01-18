theory S_R_Spark_Declaration
imports Complex_Main

begin

types round_index' = " int "
types rotate_definition' = " int => int "
consts integer__base__first'' :: " int "
consts integer__base__last'' :: " int "
consts integer__first'' :: " int "
consts integer__last'' :: " int "
consts integer__size'' :: " int "
consts j'' :: " int "
consts j___init'' :: " int "
consts j___loopinit'' :: " int "
consts rotate_amount__base__first'' :: " int "
consts rotate_amount__base__last'' :: " int "
consts rotate_amount__first'' :: " int "
consts rotate_amount__last'' :: " int "
consts rotate_amount__size'' :: " int "
consts rotate_definition___default_arr'' :: 
" rotate_definition'
"
consts rotate_definition___default_arr_element'' :: " int "
consts round_index__base__first'' :: " int "
consts round_index__base__last'' :: " int "
consts round_index__first'' :: " int "
consts round_index__last'' :: " int "
consts round_index__size'' :: " int "
consts s_values'' :: " rotate_definition' "
consts bit__not' :: " [ int , int ] => int "
consts character__pos' :: " int => int "
consts character__val' :: " int => int "
consts int___abs' :: " int => int "
consts int___div' :: " [ int , int ] => int "
consts int___exp' :: " [ int , int ] => int "
consts int___mod' :: " [ int , int ] => int "
consts int___odd' :: " int => bool "
consts int___rem' :: " [ int , int ] => int "
consts int___times' :: " [ int , int ] => int "
consts int___to_real' :: " int => real "
consts real___abs' :: " real => real "
consts real___div' :: " [ real , real ] => real "
consts real___exp' :: " [ real , int ] => real "
consts real___minus' :: " [ real , real ] => real "
consts real___plus' :: " [ real , real ] => real "
consts real___times' :: " [ real , real ] => real "
consts real___uminus' :: " real => real "
consts rotate_definition___mk_const_arr' :: 
" int => rotate_definition'
"
consts round__' :: " real => int "

end
