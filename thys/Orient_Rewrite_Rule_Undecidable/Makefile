AFP=$(shell isabelle getenv -b AFP)

jedit:
	isabelle jedit -d ${AFP} -l Polynomials Formalization.thy

binfo:
#	mv ../lics/supplementary/browser_info ~/.isabelle/Isabelle2023/
	isabelle build -d . -d ~/afp/2023/thys -b Undecidable_Termination_One_Rule_TRS
#	mv ~/.isabelle/Isabelle2023/browser_info ../lics/supplementary/
