#!/usr/bin/python

import sys, random, subprocess, time

owl = "/home/Projects/owl/build/distributions/owl-minimized-20.XX-development/bin/owl"

def read(path):
	f = open(path, "r")
	text = f.read()
	f.close
	return text
def write(path, text):
	f = open(path, "w")
	f.write(text)
	f.close()

def get_state_count(path):
	result = subprocess.run(["autfilt", path, "--stats=%s"], stdout = subprocess.PIPE, text = True)
	return int(result.stdout.strip())

def spot_generate_automaton(state_count, proposition_count):
	seed = random.randrange(0x10000)
	result = subprocess.run(["randaut", "--seed={}".format(seed), "--ba", "--states={}".format(state_count), str(proposition_count)], stdout = subprocess.PIPE, text = True)
	return result.stdout
def spot_generate_formula(proposition_count):
	seed = random.randrange(0x10000)
	result = subprocess.run(["randltl", "--seed={}".format(seed), str(proposition_count)], stdout = subprocess.PIPE, text = True)
	return result.stdout.strip()

def spot_simplify_automaton(path):
	result = subprocess.run(["autfilt", "--ba", "--small", path], stdout = subprocess.PIPE, text = True)
	return result.stdout
def owl_simplify_automaton(path):
	result = subprocess.run(["owl", "-I", path, "---", "hoa", "---", "optimize-aut", "---", "hoa", "-s"], stdout = subprocess.PIPE, text = True)
	return result.stdout

def spot_formula_to_nba(formula):
	result = subprocess.run(["ltl2tgba", "--ba", formula], stdout = subprocess.PIPE, text = True)
	return result.stdout
def owl_formula_to_nba(formula):
	result = subprocess.run(["owl", "-i", formula, "---", "ltl", "---", "simplify-ltl", "---", "ltl2nba", "---", "hoa", "-s"], stdout = subprocess.PIPE, text = True)
	return result.stdout
def owl_formula_to_dra(formula):
	result = subprocess.run(["owl", "-i", formula, "---", "ltl", "---", "simplify-ltl", "---", "ltl2dra", "---", "hoa", "-s"], stdout = subprocess.PIPE, text = True)
	return result.stdout

def bc_complement(path1, path2):
	subprocess.run(["./Autool", "complement_quick", path1, path2], timeout = 10)
def bc_equivalence(path1, path2):
	result = subprocess.run(["./Autool", "equivalence", path1, path2], timeout = 10, stdout = subprocess.PIPE, text = True)
	return result.stdout.strip() == "true"

def complement(path_input, path_output):
	start = time.time()
	try: bc_complement(path_input, path_output)
	except subprocess.TimeoutExpired: duration = "T"
	else: duration = str(time.time() - start)
	print("{} {}".format(get_state_count(path_input), duration))
def equivalence(path_1, path_2):
	start = time.time()
	try: eq = bc_equivalence(path_1, path_2)
	except subprocess.TimeoutExpired: eq = None; duration = "T"
	else: duration = str(time.time() - start)
	print("{} {} {} {}".format(get_state_count(path_1), get_state_count(path_2), eq, duration))

if sys.argv[1] == "complement_automaton":
	while True:
		write("a.hoa", spot_generate_automaton(20, 4))
		complement("a.hoa", "c.txt")
if sys.argv[1] == "complement_formula":
	while True:
		write("a.hoa", spot_formula_to_nba(spot_generate_formula(4)))
		complement("a.hoa", "c.txt")
if sys.argv[1] == "equivalence_random":
	while True:
		write("a.hoa", spot_generate_automaton(100, 4))
		write("b.hoa", spot_generate_automaton(100, 4))
		equivalence("a.hoa", "b.hoa")
if sys.argv[1] == "equivalence_simplify":
	while True:
		write("a.hoa", spot_generate_automaton(20, 4))
		write("b.hoa", spot_simplify_automaton("a.hoa"))
		equivalence("a.hoa", "b.hoa")
if sys.argv[1] == "equivalence_translate":
	while True:
		formula = spot_generate_formula(4)
		print(formula)
		write("a.hoa", owl_formula_to_nba(formula))
		write("b.hoa", owl_formula_to_dra(formula))
		write("c.hoa", spot_simplify_automaton("b.hoa"))
		if not read("c.hoa"): continue
		equivalence("a.hoa", "c.hoa")
