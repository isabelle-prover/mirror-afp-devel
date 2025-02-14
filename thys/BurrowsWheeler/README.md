# Formalized Burrows-Wheeler Transform

This a formalisation of the Burrows-Wheeler Transform (BWT) and its inverse.
This is an artefact of "L. Cheung, A. Moffat, and C. Rizkallah. 2025. Formalized Burrows-Wheeler Transform. In Proc. Certified Programs and Proofs. ACM, New York, NY, USA, 11 pages. doi:10.1145/3703595.3705883"

## Requirements:

This formalization requires the 2024 version of Isabelle, which can be downloaded from [here](https://isabelle.in.tum.de/index.html), and the `SuffixArray` entry from the AFP, which can be downloaded from [here](https://www.isa-afp.org/download/).

To install the AFP entry, run the following in the command line:

`isabelle components -u /home/myself/afp/thys`

where `isabelle` is the Isabelle executable located in the `bin` of the Isabelle application folder and `/home/myself/afp` is the location where the AFP folder that was downloaded and unzipped.

## Directory Structure:
The directory is structured as follows:

* `util` - general helper theorems
    * `Nat_Mod_Helper.thy` - theorems about modulo on natural numbers
    * `Rotated_Substring.thy` - theorems about substrings on rotations
    * `SA_Util.thy` - properties about suffix arrays
* `counting` - theorems about counting
    * `Count_Util.thy` - general counting theorems
    * `Rank_Util.thy` - definition of rank and its properties
    * `Select_Util.thy` - definition of select and its properties
    * `Rank_Select.thy` - properties about rank and select together
    * `SA_Count.thy` - properties about rank and select on suffix arrays
* `bwt` - formalisation of the BWT
    * `BWT.thy` - definition and verification of the BWT
    * `BWT_SA_Corres.thy` - theorems about the one-to-one correspondence between the BWT and suffix arrays
    * `IBWT.thy` - definition verification of the inverse BWT

## Formalization Dependencies:
This formalization depends on the formalizations of rank and select.
Their locations and links to their original work are listed below

* The formalization of rank and select in `counting/Rank_Select.thy`, while original work, draws inspiration from "R. Affeldt, J. Garrigue, X. Qi, and K. Tanaka. Proving tree algorithms for succinct data structures. In Proc. Interactive Theorem Proving, volume 141 of LIPIcs, pages 5:1–5:19. Schloss Dagstuhl - Leibniz-Zentrum für Informatik, 2019. doi:10.4230/LIPICS.ITP.2019.5".


## Running the BWT Formalisation:
To run the BWT formalization, run Isabelle and open any of the files in the `bwt` directory.
Opening the `BWT.thy` will run the proof for the BWT.
Opening the `IBWT.thy` will run the proof for the inverse BWT.

Alternatively, the following can be run in the command line:

`isabelle jedit bwt/BWT.thy`

and

`isabelle jedit bwt/IBWT.thy`

## Notes About Running the Formalisations:
Note that each of the above invocations loads the `SuffixArray` AFP entry each time. This can be avoided by building an image of the entry, which can be done by running the following instead:

`isabelle jedit -d xxx -l SuffixArray yyy`

where `xxx` is the directory of the entry and `yyy` is the relevant file.

## Key Definitions and Theorems:
All definitions and theorems that also appear in the paper are annotated with their associated definition or theorem number.
To find a specific definition/lemma/theorem, use Isabelle's search function, select the `Ignore case` and `HyperSearch` options and search for the definition/theorem with term `<Definition|Theorem> <x>`, where `<a|b>` means to choose either `a` or `b` and  `<x>` refers to the definition/theorem number presented in the paper.

Alternatively, the following list provides their locations:

* Definition 3.1: Valid
	* `valid_list`
	* From AFP `SuffixArray` entry: `Valid_List.thy` line 9
* Definition 3.2: Suffix Array Construction Characterisation
	* `Suffix_Array_General`
	* From AFP `SuffixArray` entry: `Suffix_Array.thy` line 14
* Definition 3.3: Canonical BWT
	* `bwt_canon`
	* `bwt/BWT.thy` line 10
* Definition 3.4: Suffix Array Version of the BWT
	* `bwt_sa`
	* `bwt/BWT.thy` line 17
* Theorem 3.5: Same Suffix and Rotation Order
	* `list_less_suffix_rotate`
	* `bwt/BWT.thy` line 102
* Theorem 3.6: BWT and Suffix Array Correspondence
	* `bwt_canon_eq_bwt_sa`
	* `bwt/BWT.thy` line 126
* Definition 3.7: Rank
	* `rank`
	* `counting/Rank_Util.thy` line 11
* Definition 3.8: Select
	* `select`
	* `counting/Select_Util.thy` line 10
* Theorem 3.9: Correctness of Select
	* `select_correct` 
	* `counting/Rank_Select.thy` line 26
* Theorem 3.10: Select Sorted Equivalence
	* `sorted_select` 
	* `counting/Select_Util.thy` line 272
* Theorem 3.11: Rank Equivalence
	* `rank_card_spec`
	* `counting/Rank_Util.thy` line 46
* Definition 3.12: BWT Permutation
	* `bwt_perm`
	* `bwt/BWT_SA_Corres.thy` line 11
* Theorem 3.13: Suffix Relative Order Preservation
	* `bwt_relative_order` 
	* `bwt/BWT_SA_Corres.thy` line 233
* Definition 3.14: Inverse BWT
	* `lf_map_conc`, `ibwtn`, and `ibwt` respectively 
	* `bwt/IBWT.thy` line 34, 45, 51
* Definition 3.15: Abstract LF-Mapping
	* `lf_map_abs`
	* `bwt/IBWT.thy` line 16
* Definition 3.16: Inverse BWT Permutation
	* `ibwt_perm_abs`
	* `bwt/IBWT.thy` line 21
* Theorem 3.17: Same Rank
	* `rank_same_sa_bwt_perm` 
	* `bwt/BWT_SA_Corres.thy` line 571
* Theorem 3.18: Abstract LF-mapping Correctness
	* `bwt_perm_lf_map_ab`
	* `bwt/IBWT.thy` line 245
* Theorem 3.19: Abstract Inverse BWT Permutation Rotated Sub-list
	* `is_rot_sublist_bwt_perm_ibwt_perm_abs`
	* `bwt/IBWT.thy` line 511
* Theorem 3.20: Correctness of the Inverse BWT
	* `ibwt_correct_canon`
	* `bwt/IBWT.thy` line 721

