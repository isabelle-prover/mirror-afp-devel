#!/usr/bin/python

import sys, random, subprocess, time

def read(path):
	f = open(path, "r")
	text = f.read()
	f.close
	return text
def write(path, text):
	f = open(path, "w")
	f.write(text)
	f.close()

def stats(entries, finished):
	entry_count = "{}".format(len(entries))
	finished_ratio = "{:.2f} \\%".format(100 * len(finished) / len(entries)) if entries else "N/A"
	finished_time = "{:.3f} s".format(sum(finished) / len(finished)) if finished else "N/A"
	return "{} & {} & {}".format(entry_count, finished_ratio, finished_time)
def stats_entries(entries, label, predicate):
	entries = list(time for (state_count, result, time) in entries if predicate(state_count, result, time))
	finished = list(float(time) for time in entries if time != "T")
	print("{} & {}\\\\".format(label, stats(entries, finished)))

if sys.argv[1] == "states":
	entries = list(line.split() for line in read(sys.argv[2]).splitlines())
	entries = list((int(state_count_1), int(state_count_2), result, time) for [state_count_1, state_count_2, result, time] in entries)
	non_timeout = list(time for (state_count_1, state_count_2, result, time) in entries if time != "T")
	print(all(result == "True" or time == "T" for (state_count_1, state_count_2, result, time) in entries))
	print("completion rate: {}".format(len(non_timeout) / len(entries)))
	print("{} {}".format(sum(state_count_1 for (state_count_1, state_count_2, result, time) in entries) / len(entries), sum(state_count_2 for (state_count_1, state_count_2, result, time) in entries) / len(entries)))

if sys.argv[1] == "complement":
	entries = list(line.split() for line in read(sys.argv[2]).splitlines())
	entries = list(time for [state_count, time] in entries)
	non_timeout = list(float(time) for time in entries if time != "T")
	print(stats(entries, non_timeout))
if sys.argv[1] == "equivalence":
	cutoff = 20
	entries = list(line.split() for line in read(sys.argv[2]).splitlines())
	entries = list((max(int(state_count_1), int(state_count_2)), result, time) for [state_count_1, state_count_2, result, time] in entries)
	print(all(result == "True" or time == "T" for (state_count, result, time) in entries))
	for n in range(1, cutoff + 1): stats_entries(entries, n, lambda state_count, result, time: state_count == n)
	stats_entries(entries, "> {}".format(cutoff), lambda state_count, result, time: state_count > cutoff)
	stats_entries(entries, "total", lambda state_count, result, time: True)
